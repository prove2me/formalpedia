-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.value_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:08:05.448812+00:00
-- url     : https://prove2.me/submissions/ee74550b-f2d8-4a4c-b138-bbf253a07eef

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_exists_value_eq_zpow
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_value_eq_one_of_continuous

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
theorem _root_.solution (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1)
    (hmax : ∀ x : E, valuation E x < 1 → valuation E x ≤ valuation E (algebraMap k E π))
    (τ : E ≃ₐ[k] E) (x : E) : valuation E (τ x) = valuation E x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, hm⟩ := exists_value_eq_zpow h0 h1 hmax hx
  set p := algebraMap k E π with hp
  have hy : valuation E (x * p ^ (-m)) = 1 := by
    rw [map_mul, map_zpow₀, hm, ← zpow_add₀ h0]
    simp
  have h2 := value_eq_one_of_continuous hc τ hy
  rw [map_mul, map_zpow₀ τ, hp, τ.commutes, ← hp, map_mul, map_zpow₀, zpow_neg,
    mul_inv_eq_one₀ (zpow_ne_zero _ h0)] at h2
  rw [h2, hm]
end GlobalTheory.CompanionTheory.UnramDict
