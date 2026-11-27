-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.isSeparable_genY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:14.581723+00:00
-- url     : https://prove2.me/submissions/dfa60010-0d5f-492b-be9a-65e71f1bcdc5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Theorems.Thm_GroundTheory_Arith_Abelian_isSeparable_of_quadratic
import Theorems.Thm_GroundTheory_Arith_Abelian_aeval_genX_eq_zero_iff
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian___Sq_ne_zero_d2a733e9e1e7
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
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
universe u
variable {F : Type u} [Field F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (L : IntermediateField F E.toAffine.FunctionField)
    (hL : L ≤ F⟮genX E⟯) : IsSeparable (extendScalars hL) (genY E) := by
  have hg : genX E ∈ extendScalars hL := (mem_extendScalars hL).mpr (mem_adjoin_simple_self F _)
  have hcst : ∀ a : F, algebraMap F E.toAffine.FunctionField a ∈ extendScalars hL := fun a =>
    (mem_extendScalars hL).mpr (IntermediateField.algebraMap_mem _ a)
  refine isSeparable_of_quadratic
    (⟨algebraMap F _ E.a₁ * genX E + algebraMap F _ E.a₃, add_mem (mul_mem (hcst _) hg) (hcst _)⟩)
    (⟨genX E ^ 3 + algebraMap F _ E.a₂ * genX E ^ 2 + algebraMap F _ E.a₄ * genX E +
      algebraMap F _ E.a₆, add_mem (add_mem (add_mem (pow_mem hg 3)
        (mul_mem (hcst _) (pow_mem hg 2))) (mul_mem (hcst _) hg)) (hcst _)⟩) ?_ ?_
  · have e := (equation_iff _ _).mp (equation_gen E)
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
    change genY E ^ 2 + (algebraMap F _ E.a₁ * genX E + algebraMap F _ E.a₃) * genY E -
      (genX E ^ 3 + algebraMap F _ E.a₂ * genX E ^ 2 + algebraMap F _ E.a₄ * genX E +
        algebraMap F _ E.a₆) = 0
    linear_combination e
  · intro h'
    simp only [IntermediateField.algebraMap_apply] at h'
    have : aeval (genX E) E.Ψ₂Sq = 0 := by
      rw [← h']
      simp only [Ψ₂Sq, map_add, map_mul, map_pow, aeval_C, aeval_X, b₂, b₄, b₆, map_ofNat]
      ring
    rw [aeval_genX_eq_zero_iff] at this
    exact Ψ₂Sq_ne_zero E this
end GroundTheory.Arith.Abelian
