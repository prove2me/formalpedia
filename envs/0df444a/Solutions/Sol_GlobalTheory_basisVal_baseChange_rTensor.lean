-- Prove2me | solution 1 for GlobalTheory.basisVal_baseChange_rTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:13.86618+00:00
-- url     : https://prove2.me/submissions/68307405-8d38-4edc-a15b-e92abca54fd8

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
theorem _root_.solution (w : Valuation S Γ₀) (φ : R →ₐ[O] S)
    (h : ∀ a, w (φ a) = v a) (x : R ⊗[O] M) :
    basisVal w (b.baseChange S) (φ.toLinearMap.rTensor M x) = basisVal v (b.baseChange R) x := by
  have key : ∀ i, (b.baseChange S).repr (φ.toLinearMap.rTensor M x) i =
      φ ((b.baseChange R).repr x i) := fun i => by
    induction x with
    | zero => simp
    | tmul a y => simp
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  exact eq_of_forall_ge_iff fun γ => by simp only [basisVal_le_iff, key, h]
end GlobalTheory
