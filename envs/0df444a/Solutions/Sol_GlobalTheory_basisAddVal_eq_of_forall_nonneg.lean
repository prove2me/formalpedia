-- Prove2me | solution 1 for GlobalTheory.basisAddVal_eq_of_forall_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:06.218483+00:00
-- url     : https://prove2.me/submissions/70984aa5-0656-4d1f-8e6d-790e6d44a0cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_eq_of_forall_le_one

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
variable {R Γ ι κ σ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
variable {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
namespace GlobalTheory
theorem _root_.solution (hv : ∀ a, 0 ≤ v a) (c : Basis κ R M) (x : M) :
    basisAddVal v b x = basisAddVal v c x :=
  basisVal_eq_of_forall_le_one (AddValuation.toValuation v) b hv c x
end GlobalTheory
