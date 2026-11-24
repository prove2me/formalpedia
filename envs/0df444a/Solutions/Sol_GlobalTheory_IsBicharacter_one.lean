-- Prove2me | solution 1 for GlobalTheory.IsBicharacter.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:16:01.470817+00:00
-- url     : https://prove2.me/submissions/e2d84f1b-98fa-4ac8-9e8f-b8ee11815476

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
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
open Algebra.TensorProduct (productMap)
variable (R : Type*) {H K : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
  [CommSemiring K] [Bialgebra R K]
variable {R} {u v : H ⊗[R] K}
open GlobalTheory.IsBicharacter
namespace GlobalTheory.IsBicharacter
theorem _root_.solution : IsBicharacter R (1 : H ⊗[R] K) :=
  ⟨(map_one (Algebra.TensorProduct.comm R H K)).symm ▸ IsGroupLikeElem.one, IsGroupLikeElem.one⟩
end GlobalTheory.IsBicharacter
