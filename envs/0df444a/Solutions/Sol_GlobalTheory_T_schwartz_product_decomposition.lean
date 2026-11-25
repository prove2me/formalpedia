-- Prove2me | solution 1 for GlobalTheory.T.schwartz_product_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:24:17.16782+00:00
-- url     : https://prove2.me/submissions/5bdecb03-d9f7-4739-ab7d-a8895cc6a1a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzProductDecomposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzProductDecompositionStatement
import Theorems.Thm_GlobalTheory_SBProd_exists_sum_box


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → X) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ ⊕ κ' → X) →
    ∃ (ι : Type) (_ : Fintype ι) (g₁ : ι → (κ → X) → ℂ) (g₂ : ι → (κ' → X) → ℂ),
      (∀ i, g₁ i ∈ GlobalTheory.WeilM.SB (κ → X)) ∧ (∀ i, g₂ i ∈ GlobalTheory.WeilM.SB (κ' → X)) ∧
      g = ∑ i, fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr) := by
  first | exact @GlobalTheory.SBProd.exists_sum_box | exact GlobalTheory.SBProd.exists_sum_box | (intros; apply GlobalTheory.SBProd.exists_sum_box <;> assumption)
end _root_.GlobalTheory.T
