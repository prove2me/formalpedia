-- Prove2me | solution 1 for GlobalTheory.ActDescent.exists_oAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:08:24.481999+00:00
-- url     : https://prove2.me/submissions/5767f52a-f0b5-498f-9810-7009a704687a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_OActDescendOfGenerators
import Theorems.Thm_GlobalTheory_ActDescent_over_hom_ext
import Theorems.Thm_GlobalTheory_ActDescent_isMonHom_descend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ActDescent
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]
namespace GlobalTheory.ActDescent
namespace _root_.GlobalTheory.ActDescent
theorem _root_.solution {O : Type} [CommRing O] {G : Over S} [GrpObj G]
    {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ)
    (i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G') (hi : ∀ x, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) :
    ∃ a : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  choose g hg using hi
  have hpb := hG.1
  have hmon : ∀ x, IsMonHom (g x) := fun x =>
    haveI := i.hom x
    _root_.GlobalTheory.ActDescent.isMonHom_descend hG hG (i.act x) (g x) (hg x)
  refine ⟨⟨g, hmon, ?_, ?_, ?_⟩, hg⟩
  · apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    rw [← hg, i.one]
    simp
  · intro a b
    apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    rw [← hg, i.mul, Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, hg,
      Category.assoc]
  · intro a b
    apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    let ρ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hpb.w
    have hpush : ∀ c, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG G' (i.act c) = ρ ≫ g c :=
      fun c => Over.OverMorphism.ext (by exact hg c)
    change (ρ ≫ g (a + b)).left = (ρ ≫ (g a * g b)).left
    rw [MonObj.comp_mul, ← hpush, ← hpush, ← hpush, ← map_mul, i.add]
end _root_.GlobalTheory.ActDescent
end GlobalTheory.ActDescent
