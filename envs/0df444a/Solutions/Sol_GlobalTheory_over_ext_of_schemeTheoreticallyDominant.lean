-- Prove2me | solution 1 for GlobalTheory.over_ext_of_schemeTheoreticallyDominant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:48.466321+00:00
-- url     : https://prove2.me/submissions/1c9dc834-dc4f-4dc0-a544-54316ada09d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Theorems.Thm_GlobalTheory_exists_lift_of_schemeTheoreticallyDominant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S W : Scheme.{0}} {Y X : Over S}
    [IsSeparated X.hom] (φ : W ⟶ Y.left) [IsSchemeTheoreticallyDominant φ] {a b : Y ⟶ X}
    (h : φ ≫ a.left = φ ≫ b.left) : a = b := by
  have hY : a.left ≫ X.hom = b.left ≫ X.hom := by rw [Over.w a, Over.w b]
  let e : Y.left ⟶ pullback X.hom X.hom := pullback.lift a.left b.left hY
  have he1 : e ≫ pullback.fst X.hom X.hom = a.left := pullback.lift_fst _ _ _
  have he2 : e ≫ pullback.snd X.hom X.hom = b.left := pullback.lift_snd _ _ _
  have hc : (φ ≫ a.left) ≫ pullback.diagonal X.hom = φ ≫ e := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pullback.diagonal_fst, he1, Category.comp_id]
    · simp only [Category.assoc]
      rw [pullback.diagonal_snd, he2, Category.comp_id, h]
  have hs2 : pullback.lift (φ ≫ a.left) φ hc ≫ pullback.snd (pullback.diagonal X.hom) e = φ :=
    pullback.lift_snd _ _ _
  obtain ⟨s, hs⟩ := exists_lift_of_schemeTheoreticallyDominant φ
    (pullback.snd (pullback.diagonal X.hom) e) (𝟙 _) (pullback.lift _ _ hc)
    (by rw [hs2, Category.comp_id])
  have key : ∀ g : pullback X.hom X.hom ⟶ X.left, e ≫ g =
      s ≫ pullback.fst (pullback.diagonal X.hom) e ≫ pullback.diagonal X.hom ≫ g := by
    intro g
    rw [pullback.condition_assoc, ← Category.assoc s, hs, Category.id_comp]
  have ha := key (pullback.fst X.hom X.hom)
  have hb := key (pullback.snd X.hom X.hom)
  rw [he1, pullback.diagonal_fst, Category.comp_id] at ha
  rw [he2, pullback.diagonal_snd, Category.comp_id] at hb
  exact Over.OverMorphism.ext (ha.trans hb.symm)
end GlobalTheory
