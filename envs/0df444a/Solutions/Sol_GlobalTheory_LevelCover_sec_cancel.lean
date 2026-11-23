-- Prove2me | solution 1 for GlobalTheory.LevelCover.sec_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:51.802802+00:00
-- url     : https://prove2.me/submissions/d1daeb94-2768-4d71-8756-d817df0cd2be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.LevelCover
theorem _root_.solution {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    (m' : SABMap t'' t' g) (m : SABMap t' t f) (x : 𝟙_ (Over S'') ⟶ t''.G) (y : 𝟙_ (Over S') ⟶ t'.G)
    (h : x.left ≫ m'.φ ≫ m.φ = g ≫ y.left ≫ m.φ) : x.left ≫ m'.φ = g ≫ y.left := by
  apply m.cart.1.hom_ext
  · simpa only [Category.assoc] using h
  · have a₁ : x.left ≫ t''.G.hom = 𝟙 _ := Over.w x
    have a₂ : y.left ≫ t'.G.hom = 𝟙 _ := Over.w y
    rw [Category.assoc, m'.cart.1.w, ← Category.assoc, a₁, Category.assoc, a₂]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
end GlobalTheory.LevelCover
