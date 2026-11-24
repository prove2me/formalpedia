-- Prove2me | solution 1 for GlobalTheory.gaussVal_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:04.208438+00:00
-- url     : https://prove2.me/submissions/c8efc9cd-4e2f-42e4-b8ba-3afa4f1cb854

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_coeffSup_lt_iff

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
open MvPolynomial
variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)
namespace GlobalTheory
theorem _root_.solution {f : MvPolynomial σ R} {γ : Γ₀} (hγ : γ ≠ 0) :
    gaussVal v f < γ ↔ ∀ m, v (coeff m f) < γ := coeffSup_lt_iff v.map_zero hγ
end GlobalTheory
