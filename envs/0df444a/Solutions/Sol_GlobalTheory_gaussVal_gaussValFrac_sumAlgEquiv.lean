-- Prove2me | solution 1 for GlobalTheory.gaussVal_gaussValFrac_sumAlgEquiv
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:38:04.137588+00:00
-- url     : https://prove2.me/submissions/e98feaa8-cf08-4992-9830-407bfefe3181

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
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

theorem solution (f : MvPolynomial (τ ⊕ σ) K) :
    gaussVal (gaussValFrac v σ F) (map (algebraMap _ F) (sumAlgEquiv K τ σ f)) =
      gaussVal v f := by
  have hmap (g : MvPolynomial τ (MvPolynomial σ K)) :
      gaussVal (gaussValFrac v σ F) (map (algebraMap (MvPolynomial σ K) F) g) =
        gaussVal (gaussVal v) g := by
    refine le_antisymm ?_ ?_
    · exact (gaussVal_le_iff _).mpr fun m => by
        rw [coeff_map, gaussValFrac_algebraMap (F := F)]
        exact le_gaussVal (gaussVal v) g m
    · exact (gaussVal_le_iff _).mpr fun m => by
        rw [← gaussValFrac_algebraMap (F := F), ← coeff_map]
        exact le_gaussVal _ (map (algebraMap (MvPolynomial σ K) F) g) m
  rw [hmap, gaussVal_sumAlgEquiv]
