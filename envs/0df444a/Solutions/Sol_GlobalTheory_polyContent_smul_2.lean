-- Prove2me | solution 2 for GlobalTheory.polyContent_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:05.2678+00:00
-- url     : https://prove2.me/submissions/9a0b0199-14c7-4b89-acd6-ed48a453fb22

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
theorem _root_.solution (a : R) (c : (σ →₀ ℕ) →₀ M) :
    polyContent v b (a • c) = v a * polyContent v b c :=
  coeffSup_eq_mul_of_forall (basisVal_zero v b) (basisVal_zero v b) fun m => by
    rw [Finsupp.smul_apply, basisVal_smul]
end GlobalTheory
