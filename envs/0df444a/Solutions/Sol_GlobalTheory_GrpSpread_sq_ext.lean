-- Prove2me | solution 1 for GlobalTheory.GrpSpread.sq_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:30.744952+00:00
-- url     : https://prove2.me/submissions/1f26120a-3813-439c-9dcd-beac6104d6b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.GrpSpread
open GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}
namespace GlobalTheory.GrpSpread
theorem _root_.solution {W : Scheme.{0}} {a b : W ⟶ (G ⊗ G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := by
  have hab : a ≫ (G ⊗ G).hom = b ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← Category.assoc, h₁]
  let a' : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk a rfl
  let b' : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk b hab.symm
  have e : a' = b' := CartesianMonoidalCategory.hom_ext _ _
    (Over.OverMorphism.ext (by simpa [a', b'] using h₁))
    (Over.OverMorphism.ext (by simpa [a', b'] using h₂))
  exact congrArg CommaMorphism.left e
end GlobalTheory.GrpSpread
