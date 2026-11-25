-- Prove2me | solution 1 for GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:54:59.985345+00:00
-- url     : https://prove2.me/submissions/f3d06f89-1e7c-4b5a-9536-0df3db778adc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_le_of_isIntegral
import Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_le_of_isIntegral_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
namespace GroundTheory.Arith.Toric
theorem _root_.solution (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim A = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral (ringKrullDim_le_of_isIntegral_of_injective hinj)
end GroundTheory.Arith.Toric
