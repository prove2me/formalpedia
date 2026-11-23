-- Prove2me | solution 1 for GlobalTheory.TorusNil.comp_eq_of_pullback_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:15.546621+00:00
-- url     : https://prove2.me/submissions/a1eb557f-7baf-4ed4-9939-20759fd93d81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_pullback_map_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
namespace GlobalTheory.TorusNil
theorem _root_.solution {S S' : Scheme.{0}} {p : S' ⟶ S} {Z V W : Over S}
    {f g : V ⟶ W} (h : (Over.pullback p).map f = (Over.pullback p).map g) (t : Z ⟶ V)
    (s : Z.left ⟶ S') (hs : s ≫ p = Z.hom) : t ≫ f = t ≫ g := by
  let u : Over.mk s ⟶ (Over.pullback p).obj V :=
    Over.homMk (pullback.lift t.left s ((Over.w t).trans hs.symm)) (pullback.lift_snd _ _ _)
  have hu : u.left ≫ pullback.fst V.hom p = t.left := pullback.lift_fst _ _ _
  have h1 := pullback_map_fst u f
  have h2 := pullback_map_fst u g
  rw [h, h2] at h1
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, ← hu]
  exact (Category.assoc _ _ _).trans (h1.symm.trans (Category.assoc _ _ _).symm)
end GlobalTheory.TorusNil
