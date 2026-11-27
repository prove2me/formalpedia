-- Prove2me | solution 1 for GroundTheory.Global.gaussResidue_gaussY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:40.64296+00:00
-- url     : https://prove2.me/submissions/2b64f981-e970-4905-b4bc-709be528687c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Theorems.Thm_GroundTheory_Global_gaussResidue_residue

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
    gaussResidue W (residue (gaussRing W) (gaussY W)) = genY (W.map (residue 𝒪)) := by
  rw [gaussY, gaussResidue_residue, genY]
  congr 1
  rw [CoordinateRing.map_mk, Polynomial.map_X]
end GroundTheory.Global
