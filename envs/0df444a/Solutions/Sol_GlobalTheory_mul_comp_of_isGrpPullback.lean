-- Prove2me | solution 1 for GlobalTheory.mul_comp_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:34.32251+00:00
-- url     : https://prove2.me/submissions/a6eee84f-257d-4448-a824-b6a7c8bc63bb

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GrpHomAlgebraisationOfReductions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S S' : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    {Y Z : Over S'} [GrpObj Y] [GrpObj Z] {t : S' ⟶ S} {a : Y.left ⟶ A.left} {b : Z.left ⟶ B.left}
    (ha : IsGrpPullback Y A t a) (hb : IsGrpPullback Z B t b) (f : Y ⟶ Z) [IsMonHom f] (g : A ⟶ B)
    (hg : a ≫ g.left = f.left ≫ b) (T : Over S') (x y : Over.mk (T.hom ≫ t) ⟶ A) :
    (x * y) ≫ g = (x ≫ g) * (y ≫ g) := by
  let x' : T ⟶ Y := Over.homMk (ha.1.lift x.left T.hom (Over.w x)) (ha.1.lift_snd _ _ _)
  let y' : T ⟶ Y := Over.homMk (ha.1.lift y.left T.hom (Over.w y)) (ha.1.lift_snd _ _ _)
  have hx : x.left = x'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have hy : y.left = y'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have h1 := ha.2 T x' y' x y hx hy
  have h2 := hb.2 T (x' ≫ f) (y' ≫ f) (x ≫ g) (y ≫ g)
    (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hg])
    (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hg])
  ext
  rw [h2, Over.comp_left, h1, ← MonObj.mul_comp, Over.comp_left, Category.assoc, Category.assoc, hg]
end GlobalTheory
