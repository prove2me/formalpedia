-- Prove2me | solution 1 for GlobalTheory.LieCombBaseChange.prod_left_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:37:18.283029+00:00
-- url     : https://prove2.me/submissions/5439c9df-28f4-4fd5-93bf-4d78c17c9ded

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.LieCombBaseChange
variable {R R' : Type} [CommRing R] [CommRing R']
namespace GlobalTheory.LieCombBaseChange
theorem _root_.solution {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (d : T'.left ⟶ T.left)
    (hd : d ≫ T.hom = T'.hom ≫ f) {n : ℕ} (u : Fin n → (T ⟶ G)) (u' : Fin n → (T' ⟶ G'))
    (hu : ∀ i, (u' i).left ≫ φ = d ≫ (u i).left) :
    (List.ofFn u').prod.left ≫ φ = d ≫ (List.ofFn u).prod.left := by
  have hd' : d ≫ T.hom = (Over.mk (T'.hom ≫ f)).hom := by simpa using hd
  have hsq : φ ≫ G.hom = G'.hom ≫ f := h.1.w

  have hone : (1 : T' ⟶ G').left ≫ φ = (1 : Over.mk (T'.hom ≫ f) ⟶ G).left := by
    let x₀ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk ((1 : T' ⟶ G').left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, hsq]
      rw [← Category.assoc, Over.w])
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T' 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have h1 : x₀ = 1 := by simpa using hx
    rw [← h1]
    rfl

  have key : ∀ (m : ℕ) (u : Fin m → (T ⟶ G)) (u' : Fin m → (T' ⟶ G')),
      (∀ i, (u' i).left ≫ φ = d ≫ (u i).left) →
        (List.ofFn u').prod.left ≫ φ = ((Over.homMk d hd' : Over.mk (T'.hom ≫ f) ⟶ T) ≫ (List.ofFn u).prod).left := by
    intro m
    induction m with
    | zero =>
      intro u u' _
      simp only [List.ofFn_zero, List.prod_nil, MonObj.comp_one, hone]
    | succ m ih =>
      intro u u' hu
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul]
      refine (h.2 T' _ _ _ _ ?_ ?_).symm
      · rw [Over.comp_left]
        exact (hu 0).symm
      · exact (ih _ _ fun i => hu i.succ).symm
  have := key n u u' hu
  rw [Over.comp_left] at this
  exact this
end GlobalTheory.LieCombBaseChange
