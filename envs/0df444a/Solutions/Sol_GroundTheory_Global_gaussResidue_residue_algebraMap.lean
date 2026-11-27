-- Prove2me | solution 1 for GroundTheory.Global.gaussResidue_residue_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:43.401006+00:00
-- url     : https://prove2.me/submissions/49c68e04-5156-42b6-9f4d-2e3599ac81d4

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
namespace GroundTheory.Global
theorem _root_.solution (c : 𝒪) :
    gaussResidue W (residue (gaussRing W) (algebraMap 𝒪 (gaussRing W) c)) =
      algebraMap (ResidueField 𝒪) _ (residue 𝒪 c) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 W.toAffine.CoordinateRing (gaussRing W),
    gaussResidue_residue, coordReduce_algebraMap, ← IsScalarTower.algebraMap_apply]
end GroundTheory.Global
