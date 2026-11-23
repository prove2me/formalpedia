-- Prove2me | solution 1 for GlobalTheory.basisVal_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:51.067856+00:00
-- url     : https://prove2.me/submissions/56969564-5d90-4775-91ec-a29645f4ebc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_basisVal

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
theorem _root_.solution (x y : M) :
    basisVal v b (x + y) ≤ max (basisVal v b x) (basisVal v b y) :=
  (basisVal_le_iff v b).mpr fun i => by
    rw [map_add, Finsupp.add_apply]
    exact (v.map_add _ _).trans (max_le_max (le_basisVal v b x i) (le_basisVal v b y i))
end GlobalTheory
