-- Prove2me | solution 1 for GlobalTheory.mul_mem_identityComponent_of_rational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:39.694216+00:00
-- url     : https://prove2.me/submissions/5321a518-1d57-4e8c-8c05-7e0067792e80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulMemIdentityComponentOfRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), x.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → (x * y).left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) := by
  intro k _ G _ x y hx hy
  set T : G ⟶ G := (toUnit G ≫ x) * 𝟙 G with hT
  have hyT : y ≫ T = x * y := by
    rw [hT, comp_mul, ← Category.assoc, toUnit_unique (y ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]
  have hηT : η[G] ≫ T = x := by
    rw [hT, comp_mul, ← Category.assoc, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]
    have : (η[G] : 𝟙_ _ ⟶ G) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [this, _root_.mul_one]
  have hsub := T.left.continuous.image_connectedComponent_subset ((η[G]).left (IsLocalRing.closedPoint k))
  have h1 : (x * y).left (IsLocalRing.closedPoint k) = T.left (y.left (IsLocalRing.closedPoint k)) := by
    rw [← hyT, Over.comp_left]
    exact Scheme.Hom.comp_apply y.left T.left _
  have h2 : T.left ((η[G]).left (IsLocalRing.closedPoint k)) = x.left (IsLocalRing.closedPoint k) := by
    rw [← hηT, Over.comp_left]
    exact (Scheme.Hom.comp_apply (η[G]).left T.left _).symm
  rw [h1, connectedComponent_eq hx]
  have := hsub ⟨_, hy, rfl⟩
  rwa [h2] at this
end GlobalTheory
