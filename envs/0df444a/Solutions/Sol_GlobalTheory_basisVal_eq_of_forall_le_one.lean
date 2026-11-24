-- Prove2me | solution 1 for GlobalTheory.basisVal_eq_of_forall_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:31.386488+00:00
-- url     : https://prove2.me/submissions/e6418b70-6c38-4f15-8c48-209059afdeb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_eq_of_le_one

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
theorem _root_.solution (hv : ∀ a, v a ≤ 1) (c : Basis κ R M) (x : M) :
    basisVal v b x = basisVal v c x :=
  basisVal_eq_of_le_one v b c (fun _ => (basisVal_le_iff v c).mpr fun _ => hv _)
    (fun _ => (basisVal_le_iff v b).mpr fun _ => hv _) x
end GlobalTheory
