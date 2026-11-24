-- Prove2me | solution 1 for GlobalTheory.exists_basisVal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:38:59.477502+00:00
-- url     : https://prove2.me/submissions/c8344da8-9c74-4d61-8c34-568f9192ce5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs

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
theorem _root_.solution {x : M} (hx : x ≠ 0) : ∃ i, basisVal v b x = v (b.repr x i) := by
  obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := v) (c := b.repr x) (by simpa using hx)
  exact ⟨i, hi⟩
end GlobalTheory
