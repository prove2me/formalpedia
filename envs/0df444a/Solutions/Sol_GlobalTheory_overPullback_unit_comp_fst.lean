-- Prove2me | solution 1 for GlobalTheory.overPullback_unit_comp_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:21.268115+00:00
-- url     : https://prove2.me/submissions/de51f742-7a5f-4e9e-8939-115fc841272b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMemRightTranslateMemIdentityComponentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMem

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    (η[(Over.pullback p).obj G]).left ≫ pullback.fst G.hom p = p ≫ (η[G]).left := by
  have hmap : ((Over.pullback p).map η[G]).left ≫ pullback.fst G.hom p =
      pullback.fst (𝟙_ (Over S)).hom p ≫ (η[G]).left := by
    simp; exact pullback.lift_fst _ _ _
  have hε : (Functor.LaxMonoidal.ε (Over.pullback p)).left ≫ pullback.fst (𝟙_ (Over S)).hom p = p := by
    have h1 : pullback.fst (𝟙_ (Over S)).hom p = pullback.snd (𝟙_ (Over S)).hom p ≫ p := by
      rw [← pullback.condition]; rfl
    have h2 : (Functor.LaxMonoidal.ε (Over.pullback p)).left ≫ pullback.snd (𝟙_ (Over S)).hom p = 𝟙 _ :=
      Over.w (Functor.LaxMonoidal.ε (Over.pullback p))
    rw [h1, ← Category.assoc, h2, Category.id_comp]
  show (Functor.LaxMonoidal.ε (Over.pullback p) ≫ (Over.pullback p).map η[G]).left ≫ pullback.fst G.hom p = _
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hε]
end GlobalTheory
