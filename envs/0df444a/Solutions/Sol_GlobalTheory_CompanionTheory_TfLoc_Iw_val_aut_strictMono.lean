-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.val_aut_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:09.582322+00:00
-- url     : https://prove2.me/submissions/507193a1-a0da-4c52-a0a4-fd43ed2502e2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_val_aut_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution (τ : E ≃ₐ[k] E) {a b : E} (h : valuation E a < valuation E b) :
    valuation E (τ a) < valuation E (τ b) := by
  by_contra hc
  rw [not_lt] at hc
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h
  have hτb : τ b ≠ 0 := by simpa using hb
  have hτa : τ a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact hτb ((valuation E).zero_iff.1 (le_zero_iff.1 hc))
  have ha : a ≠ 0 := by simpa using hτa
  have h1 : valuation E (τ b / τ a) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ hc zero_le'
  have h2 := val_aut_le_one τ⁻¹ h1
  have h3 : τ⁻¹ (τ b / τ a) = b / a := by
    rw [map_div₀]
    simp
  rw [h3, map_div₀] at h2
  have h4 : valuation E a ≠ 0 := (valuation E).ne_zero_iff.2 ha
  exact absurd ((div_le_one₀ (zero_lt_iff.2 h4)).1 h2) (not_le.2 h)
end GlobalTheory.CompanionTheory.TfLoc.Iw
