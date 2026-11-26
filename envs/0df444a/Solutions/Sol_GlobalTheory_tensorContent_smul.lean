-- Prove2me | solution 1 for GlobalTheory.tensorContent_smul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:46:22.729621+00:00
-- url     : https://prove2.me/submissions/8f767444-0ba7-4ddc-b9fd-669b291b3ee5

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
variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)

theorem solution (f : MvPolynomial σ R) (x : MvPolynomial σ R ⊗[O] M) :
    tensorContent v b (f • x) = gaussVal v f * tensorContent v b x := by
  unfold tensorContent
  exact basisVal_smul (gaussVal v) (b.baseChange (MvPolynomial σ R)) f x
