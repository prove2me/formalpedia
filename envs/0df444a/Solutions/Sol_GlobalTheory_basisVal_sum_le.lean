-- Prove2me | solution 1 for GlobalTheory.basisVal_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:15.63185+00:00
-- url     : https://prove2.me/submissions/8e838ebe-299f-44ab-a835-f9c2550badb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_basisVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial Module
variable {R Γ₀ ι κ σ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (b : Basis ι R M)
namespace GlobalTheory
theorem _root_.solution {α : Type*} {s : Finset α} {x : α → M} {γ : Γ₀}
    (h : ∀ a ∈ s, basisVal v b (x a) ≤ γ) : basisVal v b (∑ a ∈ s, x a) ≤ γ :=
  (basisVal_le_iff v b).mpr fun i => by
    rw [map_sum, Finsupp.finset_sum_apply]
    exact v.map_sum_le fun a ha => (le_basisVal v b _ i).trans (h a ha)
end GlobalTheory
