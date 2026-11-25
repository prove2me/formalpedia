-- Prove2me | solution 1 for GlobalTheory.Exist.ProdOpen.triv_lift_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:35.896945+00:00
-- url     : https://prove2.me/submissions/9a11e023-95f9-4884-a89a-2234658690dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivBasicOpenOfTrivFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TrivProdOfSmallExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LineBundleTrivialBasicOpenOfTrivialFibreProduct
import Theorems.Thm_GlobalTheory_Exist_ProdOpen_isPullback_prodMap
import Theorems.Thm_GlobalTheory_Exist_ProdOpen_lift_prodMap
import Theorems.Thm_GlobalTheory_Exist_ProdOpen_toUnit_section
import Theorems.Thm_GlobalTheory_Exist_ProdOpen_bijective_baseChange
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_triv_comp
import Theorems.Thm_GlobalTheory_AbLaw_CubeOpen_triv_pull_pull
import Theorems.Thm_GlobalTheory_SmallExtLift_triv_prod_of_small_extension
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.AbLaw.CubeOpen
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.ProdOpen
namespace GlobalTheory.Exist.ProdOpen
theorem _root_.solution {R : Type} [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X)
    (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y) [Flat X.hom] [Flat Y.hom] [IsProper X.hom] [IsProper Y.hom]
    (hX : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom))
    (hY : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom))
    (M : LB (X ⊗ Y).left) (hM : M.IsLB)
    (h₁ : Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left))
    (h₂ : Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left))
    (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T)
    (he : ∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) (he' : e ∈ IsLocalRing.maximalIdeal T)
    (H : ∀ (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left)
      (f' : X' ⟶ Spec (CommRingCat.of (T ⧸ Ideal.span {e}))),
      IsPullback π f' (X ⊗ Y).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ≫
          Spec.map (CommRingCat.ofHom g)) → Triv (M.pull π)) :
    Triv (M.pull (prodMap (Spec.map (CommRingCat.ofHom g)) X Y)) := by
  let φ : Sp T ⟶ Sp R := Spec.map (CommRingCat.ofHom g)
  have hp := IsPullback.of_hasPullback ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).hom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))))
  refine GlobalTheory.SmallExtLift.triv_prod_of_small_extension T e he ((Over.pullback φ).obj X) ((Over.pullback φ).obj Y)
    (Functor.LaxMonoidal.ε (Over.pullback φ) ≫ (Over.pullback φ).map x₀)
    (Functor.LaxMonoidal.ε (Over.pullback φ) ≫ (Over.pullback φ).map y₀)
    (inferInstanceAs (Flat (pullback.snd X.hom φ))) (inferInstanceAs (Flat (pullback.snd Y.hom φ)))
    (inferInstanceAs (IsProper (pullback.snd X.hom φ)))
    (inferInstanceAs (IsProper (pullback.snd Y.hom φ)))
    (bijective_baseChange g X hX) (bijective_baseChange g Y hY) (M.pull (prodMap φ X Y))
    (LB.isLB_pull hM _) ?_ ?_ _ _ _ hp he' ?_
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst X.hom φ) ?_ h₁)
    rw [← lift_prodMap, toUnit_section, CategoryTheory.Functor.map_id]
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst Y.hom φ) ?_ h₂)
    rw [← lift_prodMap, toUnit_section, CategoryTheory.Functor.map_id]
  · exact triv_pull_pull _ _ (H _ _ _ (hp.paste_horiz (isPullback_prodMap φ X Y)))
end GlobalTheory.Exist.ProdOpen
