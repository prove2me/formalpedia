-- Prove2me | solution 1 for GroundTheory.Global.coordEval_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:45.458802+00:00
-- url     : https://prove2.me/submissions/74fa8111-52e5-4033-b361-ace0812ccd03

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
noncomputable section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j]
namespace GroundTheory.Global
theorem _root_.solution (p : 𝒪[X][Y]) :
    coordEval W j hxy (CoordinateRing.mk W p) = p.eval₂ (eval₂RingHom j x) y :=
  AdjoinRoot.lift_mk _ _
end GroundTheory.Global
