-- Prove2me | solution 1 for GroundTheory.Arith.Toric.ringKrullDim_le_of_isIntegral_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:54.27453+00:00
-- url     : https://prove2.me/submissions/f8036e5a-8a43-4b62-87a6-6ed8c1e52e7c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Theorems.Thm_GroundTheory_Arith_Toric_exists_ltSeries_lift

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
    ringKrullDim R ≤ ringKrullDim A := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  obtain ⟨l', hlen, -⟩ := exists_ltSeries_lift hinj l
  exact le_iSup_of_le l' (by rw [hlen])
end GroundTheory.Arith.Toric
