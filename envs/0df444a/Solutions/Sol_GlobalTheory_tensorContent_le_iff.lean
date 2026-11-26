-- Prove2me | solution 1 for GlobalTheory.tensorContent_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:52:19.13687+00:00
-- url     : https://prove2.me/submissions/5c7dcfc9-4200-4bd3-829a-b99d0c608ffd

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

theorem solution {x : MvPolynomial σ R ⊗[O] M} {γ : Γ₀} :
    tensorContent v b x ≤ γ ↔ ∀ m, basisVal v (b.baseChange R) (tensorCoeffs x m) ≤ γ := by
  have hrepr (x : MvPolynomial σ R ⊗[O] M) (i : ι) (m : σ →₀ ℕ) :
      coeff m ((b.baseChange (MvPolynomial σ R)).repr x i) =
        (b.baseChange R).repr (tensorCoeffs x m) i := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro f y
      rw [Basis.baseChange_repr_tmul, tensorCoeffs_tmul, Basis.baseChange_repr_tmul]
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O R (MvPolynomial σ R),
        MvPolynomial.algebraMap_eq, coeff_C_mul, Algebra.smul_def]
    · intro x y hx hy
      simp [map_add, hx, hy]
  unfold tensorContent
  rw [basisVal_le_iff]
  simp_rw [gaussVal_le_iff, basisVal_le_iff, hrepr]
  exact ⟨fun h m i => h i m, fun h i m => h m i⟩
