-- Prove2me | solution 1 for GlobalTheory.CartierDual.map_map_bidual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:40.714325+00:00
-- url     : https://prove2.me/submissions/76842356-8382-4524-84d0-a7ce0d4ccc69

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
open GlobalTheory.CartierDual
variable {R H K L : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [Semiring K] [Bialgebra R K] [Module.Finite R K] [Module.Projective R K]
  [Semiring L] [Bialgebra R L] [Module.Finite R L] [Module.Projective R L]
namespace GlobalTheory.CartierDual
theorem _root_.solution (f : H →ₐc[R] K) (a : H) :
    map (map f) (bidual R H a) = bidual R K (f a) := rfl
end GlobalTheory.CartierDual
