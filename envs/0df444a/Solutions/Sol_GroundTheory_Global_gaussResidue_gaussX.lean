-- Prove2me | solution 1 for GroundTheory.Global.gaussResidue_gaussX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:37.379488+00:00
-- url     : https://prove2.me/submissions/a133cdd5-b4a1-42da-a2e4-fe1deaf070dc

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
    gaussResidue W (residue (gaussRing W) (gaussX W)) = genX (W.map (residue 𝒪)) := by
  rw [gaussX, gaussResidue_residue, genX]
  congr 1
  rw [CoordinateRing.map_mk, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]
end GroundTheory.Global
