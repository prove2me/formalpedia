-- Prove2me | solution 1 for GroundTheory.Arith.Toric.finiteType_toricAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:06.03175+00:00
-- url     : https://prove2.me/submissions/5b82a5ab-c6c3-469c-b772-49436813e644

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
import Theorems.Thm_GroundTheory_Arith_Toric_finiteType_semigroupAlgebra
import Theorems.Thm_GroundTheory_Arith_Toric_dualMonoid_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry
universe u
variable {N : Type u} [AddCommGroup N] (k : Type u) [CommRing k]
variable {k}
variable [Module.Free ℤ N] [Module.Finite ℤ N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) : Algebra.FiniteType k (toricAlgebra k σ) :=
  finiteType_semigroupAlgebra (dualMonoid_fg hσ)
end GroundTheory.Arith.Toric
