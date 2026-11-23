-- Prove2me | solution 1 for GroundTheory.Global.gaussResidue_residue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:46.200733+00:00
-- url     : https://prove2.me/submissions/d4db7458-d4b0-434d-9658-90b813d63cf3

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
namespace GroundTheory.Global
theorem _root_.solution (a : W.toAffine.CoordinateRing) :
    gaussResidue W (residue (gaussRing W) (algebraMap _ (gaussRing W) a)) =
      algebraMap _ _ (coordReduce W a) := by
  have : residue (gaussRing W) (algebraMap _ (gaussRing W) a) =
      algebraMap (W.toAffine.CoordinateRing ⧸ gaussPrime W) (gaussPrime W).ResidueField
        (Ideal.Quotient.mk _ a) := by
    rw [Ideal.algebraMap_quotient_residueField_mk,
      IsScalarTower.algebraMap_apply _ (Localization.AtPrime (gaussPrime W))
        (gaussPrime W).ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
  rw [this, gaussResidue, IsFractionRing.lift_algebraMap]
  rfl
end GroundTheory.Global
