-- Prove2me | solution 1 for GlobalTheory.polyContent_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:51:56.268339+00:00
-- url     : https://prove2.me/submissions/5f48d714-2ec9-4603-a0f8-f65b700c9af9

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
theorem _root_.solution (hv : v.supp = ⊥) {c : (σ →₀ ℕ) →₀ M} :
    polyContent v b c = 0 ↔ c = 0 := by
  first
    | (have h0 : GlobalTheory.basisVal v b 0 = 0 := by
         unfold GlobalTheory.basisVal; simp
       have key : ∀ x : M, GlobalTheory.basisVal v b x = 0 ↔ x = 0 := by
         intro x
         constructor
         · intro hx
           have h1 : ∀ i, v (b.repr x i) = 0 := fun i =>
             le_antisymm (hx ▸ (GlobalTheory.basisVal_le_iff v b).1 le_rfl i) zero_le'
           have h2 : b.repr x = 0 := by
             ext i
             have : b.repr x i ∈ v.supp := (Valuation.mem_supp_iff v _).2 (h1 i)
             rw [hv] at this
             simpa using this
           exact b.repr.map_eq_zero_iff.1 h2
         · intro hx; rw [hx, h0]
       unfold GlobalTheory.polyContent
       constructor
       · intro h
         ext m
         rw [Finsupp.zero_apply]
         refine (key _).1 (le_antisymm ?_ zero_le')
         rw [← h]
         exact GlobalTheory.le_coeffSup h0 c m
       · intro h
         rw [h, GlobalTheory.coeffSup_zero])

