-- Prove2me | solution 1 for GroundTheory.Arith.Toric.ringKrullDim_le_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:46:22.014203+00:00
-- url     : https://prove2.me/submissions/74dddeb7-034b-4f58-8270-cfc31cd94086

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension

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
theorem _root_.solution : ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ hpq =>
    Ideal.IsIntegral.comap_lt_comap (R := R) hpq
end GroundTheory.Arith.Toric
