-- Prove2me | solution 1 for GlobalTheory.extension_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:33.420601+00:00
-- url     : https://prove2.me/submissions/21e1be9a-cb96-42cd-a512-e0e0ba394179

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_ExtUnique_dense_open
import Theorems.Thm_GlobalTheory_ExtUnique_spec_fractionRing
import Theorems.Thm_GlobalTheory_ExtUnique_over_hom_ext_of_isPullback
import Theorems.Thm_GlobalTheory_ExtUnique_pullback_map_injective
import Theorems.Thm_GlobalTheory_ExtUnique_comp_eq_id_of_pullback
import Theorems.Thm_GlobalTheory_ExtUnique_isIso_of_pullback
import Theorems.Thm_GlobalTheory_ExtUnique_comp_eq_id_of_isPullback
import Theorems.Thm_GlobalTheory_ExtUnique_isIso_of_isPullback
import Theorems.Thm_GlobalTheory_ExtUnique_isMonHom_of_pullback
import Theorems.Thm_GlobalTheory_ExtUnique_mapGrp_map_injective
import Theorems.Thm_GlobalTheory_ExtUnique_isMonHom_of_isGrpPullback
import Theorems.Thm_GlobalTheory_ExtUnique_existsUnique_oAct_of_isGrpPullback
import Theorems.Thm_GlobalTheory_ExtUnique_existsUnique_oAct_pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory
open ExtUnique
namespace GlobalTheory
theorem _root_.solution :
    (∀ (S : Scheme.{0}) [IsReduced S] [IsLocallyNoetherian S] (U : S.Opens), Dense (U : Set S) →
      QuasiCompact U.ι ∧ IsSchemeTheoreticallyDominant U.ι) ∧
    (∀ (R K : Type) [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K],
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
        IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
    ∀ (U S : Scheme.{0}) (j : U ⟶ S) [QuasiCompact j] [IsSchemeTheoreticallyDominant j],
      ((∀ (X Y : Over S) [Flat X.hom] [IsSeparated Y.hom] (f g : X ⟶ Y),
          (Over.pullback j).map f = (Over.pullback j).map g → f = g) ∧
        ∀ (X Y : Over S) [Flat X.hom] [IsSeparated Y.hom] (X' : Scheme.{0}) (φ : X' ⟶ X.left) (p : X' ⟶ U),
          IsPullback φ p X.hom j → ∀ f g : X ⟶ Y, φ ≫ f.left = φ ≫ g.left → f = g) ∧
      ((∀ (G H : Over S) [GrpObj G] [GrpObj H] [Flat G.hom] [IsSeparated H.hom] (f : G ⟶ H),
          IsMonHom ((Over.pullback j).map f) → IsMonHom f) ∧
        ∀ (G H : Over S) [GrpObj G] [GrpObj H] [Flat G.hom] [IsSeparated H.hom] (G' H' : Over U) [GrpObj G']
          [GrpObj H'] (φ : G'.left ⟶ G.left) (ψ : H'.left ⟶ H.left),
          IsGrpPullback G' G j φ → IsGrpPullback H' H j ψ → ∀ (f' : G' ⟶ H') (f : G ⟶ H), IsMonHom f' →
          f'.left ≫ ψ = φ ≫ f.left → IsMonHom f) ∧
      (∀ (G H : Grp (Over S)) [Flat G.X.hom] [IsSeparated H.X.hom],
          Function.Injective ((Over.pullback j).mapGrp.map : (G ⟶ H) → _)) ∧
      ((∀ (O : Type) [CommRing O] (G : Over S) [GrpObj G] [IsCommMonObj G] [Flat G.hom] [IsSeparated G.hom]
          (i : OAct O ((Over.pullback j).obj G)), (∀ x, ∃ f : G ⟶ G, (Over.pullback j).map f = i.act x) →
          ∃! a : OAct O G, OAct.pullback j G a = i) ∧
        ∀ (O : Type) [CommRing O] (G : Over S) [GrpObj G] [Flat G.hom] [IsSeparated G.hom] (G' : Over U)
          [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G j φ → ∀ i : OAct O G',
          (∀ x, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) →
          ∃! a : OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left) ∧
      ((∀ (X Y : Over S) [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom]
          (e : (Over.pullback j).obj X ≅ (Over.pullback j).obj Y) (f : X ⟶ Y) (g : Y ⟶ X),
          (Over.pullback j).map f = e.hom → (Over.pullback j).map g = e.inv →
          IsIso f ∧ f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y) ∧
        ∀ (X Y : Over S) [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom] (X' Y' : Over U)
          (φ : X'.left ⟶ X.left) (ψ : Y'.left ⟶ Y.left), IsPullback φ X'.hom X.hom j →
          IsPullback ψ Y'.hom Y.hom j → ∀ (e : X' ≅ Y') (f : X ⟶ Y) (g : Y ⟶ X),
          e.hom.left ≫ ψ = φ ≫ f.left → e.inv.left ≫ φ = ψ ≫ g.left →
          IsIso f ∧ f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y) :=
  ⟨fun _ _ _ U hU => dense_open U hU, fun R K _ _ _ _ => spec_fractionRing R K, fun _ _ j _ _ =>
    ⟨⟨fun X Y _ _ _ _ h => pullback_map_injective j X Y h,
      fun _ _ _ _ _ _ _ h _ _ e => over_hom_ext_of_isPullback h e⟩,
    ⟨fun _ _ _ _ _ _ f h => isMonHom_of_pullback j f h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ hG hH f' f _ e => isMonHom_of_isGrpPullback hG hH f' f e⟩,
    fun G H _ _ => mapGrp_map_injective j G H,
    ⟨fun _ _ _ _ _ _ _ i hi => existsUnique_oAct_pullback j i hi,
      fun _ _ _ _ _ _ _ _ _ hG i hi => existsUnique_oAct_of_isGrpPullback hG i hi⟩,
    ⟨fun _ _ _ _ _ _ e f g hf hg => ⟨isIso_of_pullback j e f g hf hg, comp_eq_id_of_pullback j e f g hf hg⟩,
      fun _ _ _ _ _ _ _ _ _ _ hX hY e f g hf hg =>
        ⟨isIso_of_isPullback hX hY e f g hf hg, comp_eq_id_of_isPullback hX hY e f g hf hg⟩⟩⟩⟩
end GlobalTheory
