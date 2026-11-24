-- Prove2me | solution 1 for GlobalTheory.IsBicharacter.map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:14:36.781219+00:00
-- url     : https://prove2.me/submissions/455b48ac-c9b8-4b25-9648-afcf1bc04d1f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Theorems.Thm_GlobalTheory_isGroupLikeElem_tensor_map

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
variable {H K : Type*} [CommSemiring H] [Bialgebra R H] [CommSemiring K] [Bialgebra R K]
  {u : H ⊗[R] K}
namespace GlobalTheory
namespace IsBicharacter
theorem _root_.solution {H' K' : Type*} [CommSemiring H'] [Bialgebra R H'] [CommSemiring K']
    [Bialgebra R K'] (hu : IsBicharacter R u) (f : H →ₐc[R] H') (g : K →ₐc[R] K') :
    IsBicharacter R (Algebra.TensorProduct.map (f : H →ₐ[R] H') (g : K →ₐ[R] K') u) := by
  refine ⟨?_, isGroupLikeElem_tensor_map hu.right _ g⟩
  have h : TensorProduct.comm R H' K'
      (Algebra.TensorProduct.map (f : H →ₐ[R] H') (g : K →ₐ[R] K') u) =
      Algebra.TensorProduct.map (g : K →ₐ[R] K') (f : H →ₐ[R] H') (TensorProduct.comm R H K u) := by
    clear hu
    induction u with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp
  rw [h]
  exact isGroupLikeElem_tensor_map hu.left _ f
end IsBicharacter
end GlobalTheory
