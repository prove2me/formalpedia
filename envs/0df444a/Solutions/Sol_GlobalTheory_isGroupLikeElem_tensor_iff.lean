-- Prove2me | solution 1 for GlobalTheory.isGroupLikeElem_tensor_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:23.724163+00:00
-- url     : https://prove2.me/submissions/e6cf235c-55f6-469d-a20c-4673a421130a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open Algebra.TensorProduct (includeLeft includeRight productMap)
variable {R A K : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
namespace GlobalTheory
theorem _root_.solution [Semiring K] [Bialgebra R K] (x : A ⊗[R] K) :
    IsGroupLikeElem A x ↔ TensorProduct.rid R A (LinearMap.lTensor A counit x) = 1 ∧
      LinearMap.lTensor A comul x =
        Algebra.TensorProduct.map (AlgHom.id R A) (includeLeft : K →ₐ[R] K ⊗[R] K) x *
          Algebra.TensorProduct.map (AlgHom.id R A) (includeRight : K →ₐ[R] K ⊗[R] K) x := by
  have h0 : TensorProduct.rid R A (LinearMap.lTensor A counit x) = counit (R := A) x := by
    induction x with
    | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
    | add x y hx hy => simp only [LinearEquiv.map_add, LinearMap.map_add, hx, hy]
    | tmul a h => simp
  have h2 (x y : A ⊗[R] K) : AlgebraTensorModule.distribBaseChange R A K K
      (Algebra.TensorProduct.map (AlgHom.id R A) (includeLeft : K →ₐ[R] K ⊗[R] K) x *
        Algebra.TensorProduct.map (AlgHom.id R A) (includeRight : K →ₐ[R] K ⊗[R] K) y) =
      x ⊗ₜ[A] y := by
    induction x with
    | zero => simp only [map_zero, zero_mul, zero_tmul]
    | add x x' hx hx' => simp only [map_add, add_mul, add_tmul, hx, hx']
    | tmul a h =>
      induction y with
      | zero => simp only [map_zero, mul_zero, tmul_zero]
      | add y y' hy hy' => simp only [map_add, mul_add, tmul_add, hy, hy']
      | tmul b k =>
        rw [show b ⊗ₜ[R] k = b • ((1 : A) ⊗ₜ[R] k) by simp [smul_tmul'], ← smul_tmul]
        simp [smul_tmul', mul_comm]
  rw [isGroupLikeElem_iff, h0, ← (AlgebraTensorModule.distribBaseChange R A K K).injective.eq_iff,
    distribBaseChange_lTensor_comul, h2]
end GlobalTheory
