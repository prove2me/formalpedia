-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.adjoin_genX_genY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:52.213716+00:00
-- url     : https://prove2.me/submissions/6b35b68c-8c1c-4478-9b87-1862cc6adbe1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
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
theorem _root_.solution : IntermediateField.adjoin F {genX W, genY W} = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  have mem : ∀ a : W.toAffine.CoordinateRing,
      algebraMap _ W.toAffine.FunctionField a ∈ IntermediateField.adjoin F {genX W, genY W} := by
    intro a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
    | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
      refine mul_mem ?_ (pow_mem (IntermediateField.subset_adjoin F _ (by simp [genY])) _)
      induction c using Polynomial.induction_on' with
      | add p q hp hq => rw [C_add, map_add, map_add]; exact add_mem hp hq
      | monomial m d =>
        rw [← C_mul_X_pow_eq_monomial, C_mul, C_pow, map_mul, map_mul, map_pow, map_pow]
        refine mul_mem ?_ (pow_mem (IntermediateField.subset_adjoin F _ (by simp [genX])) _)
        exact IntermediateField.algebraMap_mem _ d
  exact div_mem (mem a) (mem b)
end GroundTheory.Arith.Abelian
