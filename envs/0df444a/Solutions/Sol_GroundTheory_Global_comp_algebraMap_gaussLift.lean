-- Prove2me | solution 1 for GroundTheory.Global.comp_algebraMap_gaussLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:31.418564+00:00
-- url     : https://prove2.me/submissions/1265143b-f0ac-4472-9e59-882ee5cf9c77

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift
import Theorems.Thm_GroundTheory_Global_coordEval_mk
import Theorems.Thm_GroundTheory_Global_coordEval_algebraMap
import Theorems.Thm_GroundTheory_Global_coordinateRing_ringHom_ext
import Theorems.Thm_GroundTheory_Global_gaussLift_algebraMap_base
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_Global_algebraMap_gaussX
import Theorems.Thm_GroundTheory_Global_algebraMap_gaussY
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
variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (M : Type*) [Field M]
  [Algebra Λ M]
namespace GroundTheory.Global
theorem _root_.solution (σ : (W.baseChange K).toAffine.FunctionField →+* M)
    (hσ : ∀ c : 𝒪, σ (algebraMap 𝒪 _ c) = algebraMap Λ M (j c))
    (hX : σ (genX (W.baseChange K)) = algebraMap Λ M x)
    (hY : σ (genY (W.baseChange K)) = algebraMap Λ M y) :
    σ.comp (algebraMap (gaussRing W) _) = (algebraMap Λ M).comp (gaussLift W j hxy hx) := by
  apply IsLocalization.ringHom_ext (gaussPrime W).primeCompl
  apply coordinateRing_ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, gaussLift_algebraMap,
      coordEval_algebraMap, hσ, gaussLift_algebraMap_base]
  · simp only [RingHom.comp_apply, gaussLift_algebraMap, coordEval_mk]
    rw [← gaussX, algebraMap_gaussX, hX]
    simp
  · simp only [RingHom.comp_apply, gaussLift_algebraMap, coordEval_mk]
    rw [← gaussY, algebraMap_gaussY, hY]
    simp
end GroundTheory.Global
