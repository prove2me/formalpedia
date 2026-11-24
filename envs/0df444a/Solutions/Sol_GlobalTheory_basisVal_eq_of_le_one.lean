-- Prove2me | solution 1 for GlobalTheory.basisVal_eq_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:38.32529+00:00
-- url     : https://prove2.me/submissions/8ec3bb42-e5b9-40bb-9f3e-a5c032aa2cd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_map_le

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
theorem _root_.solution (c : Basis κ R M) (h : ∀ i, basisVal v c (b i) ≤ 1)
    (h' : ∀ j, basisVal v b (c j) ≤ 1) (x : M) : basisVal v b x = basisVal v c x :=
  le_antisymm (basisVal_map_le v c b LinearMap.id h' x) (basisVal_map_le v b c LinearMap.id h x)
end GlobalTheory
