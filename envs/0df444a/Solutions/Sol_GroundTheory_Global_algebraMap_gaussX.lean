-- Prove2me | solution 1 for GroundTheory.Global.algebraMap_gaussX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:05.533813+00:00
-- url     : https://prove2.me/submissions/ed2f039f-543d-42b5-a3b5-28347ee71452

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
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussX W) =
      genX (W.baseChange K) := by
  rw [gaussX, algebraMap_gaussRing_functionField, genX]
  congr 1
  change CoordinateRing.map W (algebraMap 𝒪 K) _ = _
  rw [CoordinateRing.map_mk, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]
  rfl
end GroundTheory.Global
