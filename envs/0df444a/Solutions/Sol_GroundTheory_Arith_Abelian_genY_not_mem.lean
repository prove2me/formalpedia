-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.genY_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:34:31.774121+00:00
-- url     : https://prove2.me/submissions/9915921a-e37d-4c7f-bb8c-542daafd59c5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Theorems.Thm_GroundTheory_Arith_Abelian_genX_eq
import Theorems.Thm_GroundTheory_Arith_Abelian_genY_ne_zero
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : genY W ∉ IntermediateField.adjoin F {genX W} := by
  intro h
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff F (genY W)).mp h
  by_cases hs : aeval (genX W) s = 0
  · rw [hs, div_zero] at hrs; exact genY_ne_zero W hrs
  have key : genY W * aeval (genX W) s = aeval (genX W) r := by rw [hrs, div_mul_cancel₀ _ hs]
  simp only [genX_eq, aeval_algebraMap_apply, aeval_X_left, AlgHom.id_apply, genY] at key hs
  rw [IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField,
    IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField,
    ← map_mul, (IsFractionRing.injective _ _).eq_iff] at key
  have h0 : (-r) • (1 : W.toAffine.CoordinateRing) + s • CoordinateRing.mk W Y = 0 := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_neg]; linear_combination key
  exact hs (by rw [(CoordinateRing.smul_basis_eq_zero h0).2, map_zero])
end GroundTheory.Arith.Abelian
