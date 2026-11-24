-- Prove2me | solution 1 for GlobalTheory.isGroupLikeElem_tensor_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:34.724795+00:00
-- url     : https://prove2.me/submissions/517d852a-33b6-4e83-819f-51b87c8f31c8

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Theorems.Thm_GlobalTheory_isGroupLikeElem_tensor_iff
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one


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
open CartierDual
variable {R : Type*} [CommSemiring R]
namespace GlobalTheory
theorem _root_.solution {A B K K' : Type*} [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] [Semiring K] [Bialgebra R K] [Semiring K'] [Bialgebra R K']
    {x : A ⊗[R] K} (hx : IsGroupLikeElem A x) (g : A →ₐ[R] B) (f : K →ₐc[R] K') :
    IsGroupLikeElem B (Algebra.TensorProduct.map g (f : K →ₐ[R] K') x) := by
  obtain ⟨h1, h2⟩ := (isGroupLikeElem_tensor_iff x).1 hx
  have e1 (x : A ⊗[R] K) : TensorProduct.rid R B
      (LinearMap.lTensor B counit (Algebra.TensorProduct.map g (f : K →ₐ[R] K') x)) =
      g (TensorProduct.rid R A (LinearMap.lTensor A counit x)) := by
    induction x with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a k => simp
  have e2 (x : A ⊗[R] K) :
      LinearMap.lTensor B comul (Algebra.TensorProduct.map g (f : K →ₐ[R] K') x) =
      Algebra.TensorProduct.map g (Algebra.TensorProduct.map (f : K →ₐ[R] K') (f : K →ₐ[R] K'))
        (LinearMap.lTensor A comul x) := by
    induction x with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a k =>
      rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
        Algebra.TensorProduct.map_tmul]
      exact congrArg _ (CoalgHomClass.map_comp_comul_apply f k).symm
  refine (isGroupLikeElem_tensor_iff _).2 ⟨by rw [e1, h1, map_one], ?_⟩
  rw [e2, h2, map_mul]
  congr 1
  · rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]; congr 1
    ext <;> simp [Algebra.TensorProduct.one_def]
  · rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]; congr 1
    ext <;> simp [Algebra.TensorProduct.one_def]
end GlobalTheory
