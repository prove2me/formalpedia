-- Prove2me | solution 1 for GlobalTheory.basisAddVal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:09.629031+00:00
-- url     : https://prove2.me/submissions/62e5efb0-7d59-4df8-85b5-7334ca10f7ae

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
variable {R Γ ι κ σ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
variable {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
namespace GlobalTheory
theorem _root_.solution (a : R) (x : M) :
    basisAddVal v b (a • x) = v a + basisAddVal v b x :=
  basisVal_smul (AddValuation.toValuation v) b a x
end GlobalTheory
