-- Prove2me | solution 1 for GlobalTheory.basisVal_eq_sup_univ
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:29:48.339632+00:00
-- url     : https://prove2.me/submissions/864a2ed7-b717-427f-8cf8-2e2fd42db819

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
variable {R Γ₀ ι κ σ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (b : Basis ι R M)
theorem _root_.solution [Fintype ι] (x : M) :
    basisVal v b x = Finset.univ.sup fun i => v (b.repr x i) := by
  first
    | (refine le_antisymm ?_ ?_
       · rw [GlobalTheory.basisVal_le_iff]
         intro i
         exact Finset.le_sup (f := fun i => v (b.repr x i)) (Finset.mem_univ i)
       · refine Finset.sup_le fun i _ => ?_
         exact (GlobalTheory.basisVal_le_iff v b).1 le_rfl i)
    | (refine le_antisymm ?_ ?_
       · rw [GlobalTheory.basisVal_le_iff]
         intro i
         exact Finset.le_sup (f := fun i => v (b.repr x i)) (Finset.mem_univ i)
       · refine Finset.sup_le fun i _ => ?_
         exact (GlobalTheory.basisVal_le_iff (v := v) (b := b)).1 le_rfl i)

