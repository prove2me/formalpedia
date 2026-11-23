-- Prove2me | solution 1 for GroundTheory.Global.algebraMap_gaussRing_functionField
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:20.572494+00:00
-- url     : https://prove2.me/submissions/067cdcac-ae56-4b1c-a96d-6e865c74a985

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss

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
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)
variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
namespace GroundTheory.Global
theorem _root_.solution (a : W.toAffine.CoordinateRing) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField
      (algebraMap W.toAffine.CoordinateRing _ a) =
        algebraMap (W.baseChange K).toAffine.CoordinateRing _ (coordBase W K a) := by
  rw [← IsScalarTower.algebraMap_apply, algebraMap_coordinateRing_functionField]
end GroundTheory.Global
