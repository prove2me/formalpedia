-- Prove2me | solution 1 for GlobalTheory.basisVal_baseChange_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:11.705511+00:00
-- url     : https://prove2.me/submissions/0b1f30e7-899a-4cc0-9d71-c3fdcaa6d0e9

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
theorem _root_.solution (y : M) :
    basisVal v (b.baseChange R) (1 ⊗ₜ y) = basisVal (v.comap (algebraMap O R)) b y :=
  eq_of_forall_ge_iff fun γ => by simp [basisVal_le_iff, Algebra.smul_def]
end GlobalTheory
