-- Prove2me | solution 1 for GlobalTheory.tensorAddContent_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:47.529315+00:00
-- url     : https://prove2.me/submissions/5078ab2b-d97b-4490-b287-b086c0c2b9b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisAddVal_smul

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
variable {O M : Type*} [CommRing O] [Algebra O R] [AddCommGroup M] [Module O M] (b : Basis ι O M)
namespace GlobalTheory
theorem _root_.solution (f : MvPolynomial σ R) (x : MvPolynomial σ R ⊗[O] M) :
    tensorAddContent v b (f • x) = gaussAddVal v f + tensorAddContent v b x :=
  basisAddVal_smul _ _ f x
end GlobalTheory
