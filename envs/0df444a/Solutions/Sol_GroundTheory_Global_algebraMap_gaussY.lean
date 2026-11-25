-- Prove2me | solution 1 for GroundTheory.Global.algebraMap_gaussY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:50.80234+00:00
-- url     : https://prove2.me/submissions/3144d931-e2d3-4c50-ada6-a4ef07ce92db

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Theorems.Thm_GroundTheory_Global_algebraMap_gaussRing_functionField

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
theorem _root_.solution :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussY W) =
      genY (W.baseChange K) := by
  rw [gaussY, algebraMap_gaussRing_functionField, genY]
  congr 1
  change CoordinateRing.map W (algebraMap 𝒪 K) _ = _
  rw [CoordinateRing.map_mk, Polynomial.map_X]
  rfl
end GroundTheory.Global
