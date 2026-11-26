-- Prove2me | solution 1 for GlobalTheory.basisVal_gaussValFrac
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:41:51.790511+00:00
-- url     : https://prove2.me/submissions/3a4d6c63-0fd2-4675-ac99-b7274fef1df2

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
open MvPolynomial Module IsDedekindDomain

theorem solution {O K Γ₀ ι σ F M : Type*} [CommRing O] [Field K] [Algebra O K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F] [Algebra O F]
    [IsScalarTower O (MvPolynomial σ K) F] [AddCommGroup M] [Module O M] (b : Basis ι O M)
    (x : MvPolynomial σ K ⊗[O] M) :
    basisVal (gaussValFrac v σ F) (b.baseChange F)
      ((IsScalarTower.toAlgHom O (MvPolynomial σ K) F).toLinearMap.rTensor M x) =
      tensorContent v b x := by
  set φ := (IsScalarTower.toAlgHom O (MvPolynomial σ K) F).toLinearMap
  have hrepr (x : MvPolynomial σ K ⊗[O] M) (i : ι) :
      (b.baseChange F).repr (φ.rTensor M x) i =
        algebraMap (MvPolynomial σ K) F ((b.baseChange (MvPolynomial σ K)).repr x i) := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro f y
      rw [LinearMap.rTensor_tmul, Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul]
      exact (φ.map_smul (b.repr y i) f).symm
    · intro x₁ x₂ hx₁ hx₂
      simp [hx₁, hx₂]
  unfold tensorContent
  refine le_antisymm ?_ ?_
  · rw [basisVal_le_iff]
    intro i
    rw [hrepr, gaussValFrac_algebraMap]
    exact (basisVal_le_iff (gaussVal v) (b.baseChange (MvPolynomial σ K))).mp le_rfl i
  · rw [basisVal_le_iff]
    intro i
    rw [← gaussValFrac_algebraMap (F := F), ← hrepr]
    exact (basisVal_le_iff (gaussValFrac v σ F) (b.baseChange F)).mp le_rfl i
