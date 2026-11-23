-- Prove2me | solution 1 for GroundTheory.Global.coordEval_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:21.191686+00:00
-- url     : https://prove2.me/submissions/bd96f59e-038a-49b6-9499-5b0953955f2e

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
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j]
namespace GroundTheory.Global
theorem _root_.solution (c : 𝒪) :
    coordEval W j hxy (algebraMap 𝒪 W.toAffine.CoordinateRing c) = j c := by
  rw [IsScalarTower.algebraMap_apply 𝒪 𝒪[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
    coordEval, AdjoinRoot.lift_of]
  simp
end GroundTheory.Global
