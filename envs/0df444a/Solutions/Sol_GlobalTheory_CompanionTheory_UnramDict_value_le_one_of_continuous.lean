-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.value_le_one_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:29.049841+00:00
-- url     : https://prove2.me/submissions/71383508-e419-4718-b16a-fec4094c2e16

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_value_lt_one_of_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict
variable {k E : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra k E]
namespace GlobalTheory.CompanionTheory.UnramDict
theorem _root_.solution (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) (τ : E ≃ₐ[k] E) {x : E}
    (hx : valuation E x ≤ 1) : valuation E (τ x) ≤ 1 := by
  by_contra h
  have h1 : 1 < valuation E (τ x) := not_le.1 h
  have hy0 : valuation E (τ x) ≠ 0 := (zero_lt_one.trans h1).ne'
  have h2 : valuation E (τ x)⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1
  have h3 := value_lt_one_of_continuous τ.symm (hc _) h2
  rw [map_inv₀, AlgEquiv.symm_apply_apply, map_inv₀] at h3
  have hx0 : valuation E x ≠ 0 := by
    intro h0
    have : x = 0 := (Valuation.zero_iff _).1 h0
    simp [this] at hy0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 hx0)).1 h3) (not_lt.2 hx)
end GlobalTheory.CompanionTheory.UnramDict
