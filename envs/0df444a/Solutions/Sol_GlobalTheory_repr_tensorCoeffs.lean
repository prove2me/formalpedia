-- Prove2me | solution 1 for GlobalTheory.repr_tensorCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:27.813833+00:00
-- url     : https://prove2.me/submissions/36557cd0-2e9e-4938-af74-e3fd4d252859

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
namespace GlobalTheory
theorem _root_.solution (x : MvPolynomial σ R ⊗[O] M) (m : σ →₀ ℕ) (i : ι) :
    (b.baseChange R).repr (tensorCoeffs x m) i =
      coeff m ((b.baseChange (MvPolynomial σ R)).repr x i) := by
  induction x with
  | zero => simp
  | tmul f y => simp
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz, coeff_add]
end GlobalTheory
