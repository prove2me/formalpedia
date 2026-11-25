-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.powAdjoin_succ_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:51:23.906261+00:00
-- url     : https://prove2.me/submissions/c8be96e2-effc-4c49-923d-0830e8d6b2f4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobeniusSep
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
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (M : IntermediateField F E.toAffine.FunctionField)
    (h1 : powAdjoin E p M 1 = ⊤) {a : ℕ} (ha : powAdjoin E p M a = ⊤) :
    powAdjoin E p M (a + 1) = ⊤ := by
  set T := powAdjoin E p M (a + 1) with hT
  let Q : IntermediateField M E.toAffine.FunctionField :=
    (T.toSubfield.comap (frobenius E.toAffine.FunctionField p)).toIntermediateField fun m => by
      show (algebraMap M E.toAffine.FunctionField m) ^ p ∈ T
      rw [← map_pow]
      exact IntermediateField.algebraMap_mem T _
  have hQ : powAdjoin E p M a ≤ Q := by
    rw [powAdjoin, adjoin_le_iff]
    rintro w (rfl | rfl)
    · show (genX E ^ p ^ a) ^ p ∈ T
      rw [← pow_mul, ← pow_succ]
      exact subset_adjoin _ _ (by simp)
    · show (genY E ^ p ^ a) ^ p ∈ T
      rw [← pow_mul, ← pow_succ]
      exact subset_adjoin _ _ (by simp)
  have hall : ∀ z : E.toAffine.FunctionField, z ^ p ∈ T := fun z =>
    hQ (show z ∈ powAdjoin E p M a by rw [ha]; trivial)
  have h1le : powAdjoin E p M 1 ≤ T := by
    rw [powAdjoin, adjoin_le_iff]
    rintro w (rfl | rfl)
    · rw [pow_one]; exact hall _
    · rw [pow_one]; exact hall _
  rw [h1] at h1le
  exact top_le_iff.mp h1le
end GroundTheory.Arith.Abelian
