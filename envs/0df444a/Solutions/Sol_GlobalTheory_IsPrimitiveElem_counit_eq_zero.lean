-- Prove2me | solution 1 for GlobalTheory.IsPrimitiveElem.counit_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:54:01.705808+00:00
-- url     : https://prove2.me/submissions/d63cc839-4a18-46b7-9f06-6ebd104275f8

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
namespace GlobalTheory
namespace IsPrimitiveElem
theorem _root_.solution {R H : Type*} [CommRing R] [Semiring H] [Bialgebra R H]
    {a : H} (ha : IsPrimitiveElem R a) : counit (R := R) a = 0 := by
  have h := congr(counit (R := R) (TensorProduct.lid R H
    $(ha ▸ rTensor_counit_comul (R := R) a)))
  simpa using h
end IsPrimitiveElem
end GlobalTheory
