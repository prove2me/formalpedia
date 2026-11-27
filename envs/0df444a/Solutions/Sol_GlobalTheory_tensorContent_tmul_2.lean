-- Prove2me | solution 2 for GlobalTheory.tensorContent_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:31.121593+00:00
-- url     : https://prove2.me/submissions/a23f1200-3eb3-4ca7-bfda-87b7e4cdcad9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_basisVal_baseChange_one_tmul

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
theorem _root_.solution (f : MvPolynomial σ R) (y : M) :
    tensorContent v b (f ⊗ₜ y) = gaussVal v f * basisVal (v.comap (algebraMap O R)) b y := by
  have : (gaussVal (σ := σ) v).comap (algebraMap O (MvPolynomial σ R)) =
      v.comap (algebraMap O R) := by
    ext a; simp
  rw [← this, ← basisVal_baseChange_one_tmul, ← basisVal_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one, tensorContent]
end GlobalTheory
