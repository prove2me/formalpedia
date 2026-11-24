-- Prove2me | solution 1 for GlobalTheory.GrpLoc.mul_left_pre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:53.006334+00:00
-- url     : https://prove2.me/submissions/01d79015-22e3-4e85-b02b-1a6ce280ecc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsGrpPullbackLocalOnBase

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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.GrpLoc
namespace GlobalTheory.GrpLoc
theorem _root_.solution {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (k : T'.left ⟶ T.left)
    (hk : k ≫ T.hom = T'.hom) (x y : T ⟶ G) (x' y' : T' ⟶ G) (hx : x'.left = k ≫ x.left)
    (hy : y'.left = k ≫ y.left) : (x' * y').left = k ≫ (x * y).left := by
  have ex : x' = Over.homMk k hk ≫ x := by ext; simp [hx]
  have ey : y' = Over.homMk k hk ≫ y := by ext; simp [hy]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left]
  rfl
end GlobalTheory.GrpLoc
