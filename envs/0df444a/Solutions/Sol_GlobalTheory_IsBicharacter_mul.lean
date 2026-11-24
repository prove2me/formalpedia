-- Prove2me | solution 1 for GlobalTheory.IsBicharacter.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:34.653073+00:00
-- url     : https://prove2.me/submissions/4ad69cd3-b9b4-401d-81a8-30e54af2a9a7

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
open CartierDual
open Algebra.TensorProduct (productMap)
variable (R : Type*) {H K : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
  [CommSemiring K] [Bialgebra R K]
variable {R} {u v : H ⊗[R] K}
open GlobalTheory.IsBicharacter
namespace GlobalTheory.IsBicharacter
theorem _root_.solution (hu : IsBicharacter R u) (hv : IsBicharacter R v) : IsBicharacter R (u * v) :=
  ⟨(map_mul (Algebra.TensorProduct.comm R H K) u v).symm ▸ hu.left.mul hv.left,
    hu.right.mul hv.right⟩
end GlobalTheory.IsBicharacter
