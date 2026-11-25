-- Prove2me | solution 1 for GlobalTheory.GrpSpread.isSquare_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:48:21.918905+00:00
-- url     : https://prove2.me/submissions/f6a0af8c-7973-4556-9629-c8d8cef3b41a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebra

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
theorem _root_.solution (w : φ ≫ G.hom = A.hom ≫ j) : IsSquare φ (sq w) := by
  constructor
  · simp only [sq]
    rw [← Over.comp_left, lift_fst]
    rfl
  · simp only [sq]
    rw [← Over.comp_left, lift_snd]
    rfl
end GlobalTheory.GrpSpread
