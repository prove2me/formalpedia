-- Prove2me | solution 1 for GroundTheory.Global.gaussLift_algebraMap_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:47.709172+00:00
-- url     : https://prove2.me/submissions/da14f1b9-9fb8-4b2d-b392-61e2ec8ab6f1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift
import Theorems.Thm_GroundTheory_Global_coordEval_algebraMap

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
variable (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))
namespace GroundTheory.Global
theorem _root_.solution (c : 𝒪) :
    gaussLift W j hxy hx (algebraMap 𝒪 (gaussRing W) c) = j c := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussLift_algebraMap, coordEval_algebraMap]
end GroundTheory.Global
