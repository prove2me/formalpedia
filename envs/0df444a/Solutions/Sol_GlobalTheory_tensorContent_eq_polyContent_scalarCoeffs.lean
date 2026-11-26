-- Prove2me | solution 1 for GlobalTheory.tensorContent_eq_polyContent_scalarCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:55:56.581922+00:00
-- url     : https://prove2.me/submissions/73aafb18-7ab5-4f5f-b4d7-33d925767c71

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

theorem solution {N : Type*} [AddCommGroup N] [Module R N]
    (c : Basis ι R N) (x : MvPolynomial σ R ⊗[R] N) :
    tensorContent v c x = polyContent v c (scalarCoeffs x) := by
  have hrepr (x : MvPolynomial σ R ⊗[R] N) (i : ι) (m : σ →₀ ℕ) :
      coeff m ((c.baseChange (MvPolynomial σ R)).repr x i) =
        c.repr (scalarCoeffs x m) i := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro f y
      rw [Basis.baseChange_repr_tmul, scalarCoeffs_tmul, Algebra.smul_def,
        MvPolynomial.algebraMap_eq, coeff_C_mul, map_smul, Finsupp.smul_apply, smul_eq_mul,
        mul_comm]
    · intro x y hx hy
      simp [map_add, hx, hy]
  have hiff (x : MvPolynomial σ R ⊗[R] N) (γ : Γ₀) :
      tensorContent v c x ≤ γ ↔ polyContent v c (scalarCoeffs x) ≤ γ := by
    unfold tensorContent polyContent
    rw [basisVal_le_iff, coeffSup_le_iff (basisVal_zero v c)]
    simp_rw [gaussVal_le_iff, basisVal_le_iff, hrepr]
    exact ⟨fun h m i => h i m, fun h i m => h m i⟩
  exact le_antisymm ((hiff x _).mpr le_rfl) ((hiff x _).mp le_rfl)
