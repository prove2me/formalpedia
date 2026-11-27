-- Prove2me | solution 1 for GroundTheory.Arith.Toric.topologicalKrullDim_affineToricVariety
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:42:46.830662+00:00
-- url     : https://prove2.me/submissions/13d68218-81ec-4674-9396-844ff0680847

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_toricAlgebra

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
variable {k N : Type u} [Field k] [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hs : (σ : ConvexCone ℝ (ℝ ⊗[ℤ] N)).Salient) :
    topologicalKrullDim (PrimeSpectrum (toricAlgebra k σ)) = Module.finrank ℤ N := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_toricAlgebra hσ hs]
end GroundTheory.Arith.Toric
