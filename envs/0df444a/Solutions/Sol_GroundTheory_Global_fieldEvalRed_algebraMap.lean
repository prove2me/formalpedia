-- Prove2me | solution 1 for GroundTheory.Global.fieldEvalRed_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:30.530413+00:00
-- url     : https://prove2.me/submissions/02ba1efb-e8b9-44cc-91d3-d2d45da5bc69

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
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
theorem _root_.solution (c : ResidueField 𝒪) :
    fieldEvalRed W j hxy hx (algebraMap (ResidueField 𝒪) _ c) = ResidueField.map j c := by
  rw [IsScalarTower.algebraMap_apply (ResidueField 𝒪) (W.map (residue 𝒪)).toAffine.CoordinateRing,
    fieldEvalRed, IsFractionRing.lift_algebraMap, IsScalarTower.algebraMap_apply (ResidueField 𝒪)
      (ResidueField 𝒪)[X], AdjoinRoot.algebraMap_eq, coordEvalRed, AdjoinRoot.lift_of]
  simp
end GroundTheory.Global
