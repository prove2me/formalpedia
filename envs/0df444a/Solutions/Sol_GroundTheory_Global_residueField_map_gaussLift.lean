-- Prove2me | solution 1 for GroundTheory.Global.residueField_map_gaussLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:47:15.835718+00:00
-- url     : https://prove2.me/submissions/84a8a454-11b4-44ad-8559-c5278eac1b1a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_Global_gaussResidue_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



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
theorem _root_.solution :
    ResidueField.map (gaussLift W j hxy hx) = (fieldEvalRed W j hxy hx).comp (gaussResidue W) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (W.toAffine.CoordinateRing ⧸ gaussPrime W))
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, Ideal.algebraMap_quotient_residueField_mk]
  have e : algebraMap W.toAffine.CoordinateRing (gaussPrime W).ResidueField a =
      residue (gaussRing W) (algebraMap _ (gaussRing W) a) := by
    rw [IsScalarTower.algebraMap_apply _ (Localization.AtPrime (gaussPrime W))
      (gaussPrime W).ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
  rw [e, ResidueField.map_residue, gaussLift_algebraMap, gaussResidue_residue, fieldEvalRed,
    IsFractionRing.lift_algebraMap, residue_coordEval]
end GroundTheory.Global
