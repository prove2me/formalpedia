-- Prove2me | solution 1 for GlobalTheory.KeyPow.KeyRule.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:22.614802+00:00
-- url     : https://prove2.me/submissions/c837e6b3-019d-45b5-8449-657437c786cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Theorems.Thm_GlobalTheory_KeyPow_ClauseH_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
namespace GlobalTheory.KeyPow
namespace KeyRule
theorem _root_.solution {N : ℕ → ℕ} {g₀ g₁ : ℕ} {S S' : ∀ g : ℕ, (Fin g → ℂ) → (Fin g → ℂ) → Prop}
    (h : KeyRule N g₀ S) (hg : g₀ ≤ g₁) (hS : ∀ g a b, g₁ ≤ g → S' g a b → S g a b) : KeyRule N g₁ S' := by
  obtain ⟨κ, h1, h2, h3, h4⟩ := h
  refine ⟨κ, fun K _ _ => (h1 K).mono hg, ?_, ?_, ?_⟩
  · intro K K' _ _ _ _ f x x' hx
    exact h2 K K' f x x' (hg.trans hx)
  · intro R K _ _ _ _ _ _ _ x xK hx
    exact h3 R K x xK (hg.trans hx)
  · intro x τ a b hx hs
    exact h4 x τ a b (hg.trans hx) (hS _ a b hx hs)
end KeyRule
end GlobalTheory.KeyPow
