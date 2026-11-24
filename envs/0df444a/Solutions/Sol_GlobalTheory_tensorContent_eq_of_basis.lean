-- Prove2me | solution 1 for GlobalTheory.tensorContent_eq_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:57.55258+00:00
-- url     : https://prove2.me/submissions/a16f598b-9155-4ac1-b0cb-b0312678e736

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_baseChange_eq

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
variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)
namespace GlobalTheory
theorem _root_.solution (hv : ∀ a : O, v (algebraMap O R a) ≤ 1) (c : Basis κ O M)
    (x : MvPolynomial σ R ⊗[O] M) : tensorContent v b x = tensorContent v c x :=
  basisVal_baseChange_eq _ b (fun a => by simpa using hv a) c x
end GlobalTheory
