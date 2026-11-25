-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeOpen.triv_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:24.845187+00:00
-- url     : https://prove2.me/submissions/2797ec6e-280a-4ce0-8d71-2e15c399b929

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_triv_comp
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_triv_pull_pull
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_isPullback_sqMap
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_lift_sqMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeOpen
namespace GlobalTheory.AbLaw.CubeOpen
theorem _root_.solution (hobs : ∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → (∃ t : LB.Gen (M.pull (lift (𝟙 A) 1).left), t.IsGen) → (∃ t : LB.Gen (M.pull (lift 1 (𝟙 A)).left), t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (A ⊗ A).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → (∃ t : LB.Gen (M.pull π), t.IsGen) → ∃ t : LB.Gen M, t.IsGen)
    {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (M : LB (A ⊗ A).left)
    (hM : M.IsLB) (h₁ : Triv (M.pull (lift (𝟙 A) 1).left)) (h₂ : Triv (M.pull (lift 1 (𝟙 A)).left))
    (T : Type) [CommRing T] [IsLocalRing T] (φ : Spec (CommRingCat.of T) ⟶ S) (e : T)
    (he : ∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) (he' : e ∈ IsLocalRing.maximalIdeal T)
    (H : ∀ (X' : Scheme.{0}) (π : X' ⟶ (A ⊗ A).left)
      (f' : X' ⟶ Spec (CommRingCat.of (T ⧸ Ideal.span {e}))),
      IsPullback π f' (A ⊗ A).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ≫ φ) → Triv (M.pull π)) :
    Triv (M.pull (sqMap φ A)) := by
  have hp := IsPullback.of_hasPullback ((Over.pullback φ).obj A ⊗ (Over.pullback φ).obj A).hom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))))
  refine hobs T e he ((Over.pullback φ).obj A) (TLinPf.isAb_pullback φ A hA) (M.pull (sqMap φ A))
    (LB.isLB_pull hM _) ?_ ?_ _ _ _ hp he' ?_
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst A.hom φ) ?_ h₁)
    rw [← lift_sqMap, Functor.map_one, CategoryTheory.Functor.map_id]
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst A.hom φ) ?_ h₂)
    rw [← lift_sqMap, Functor.map_one, CategoryTheory.Functor.map_id]
  · exact triv_pull_pull _ _ (H _ _ _ (hp.paste_horiz (isPullback_sqMap φ A)))
end GlobalTheory.AbLaw.CubeOpen
