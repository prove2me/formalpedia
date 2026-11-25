-- Prove2me | solution 1 for GlobalTheory.adjPair3_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:07:56.909046+00:00
-- url     : https://prove2.me/submissions/6b03b77c-92b2-4859-8886-d2243d23f9d6

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GrpPullbackSquareProductLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {σ : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G σ φ)
omit [IsCommMonObj G] [IsCommMonObj G']
namespace GlobalTheory
theorem _root_.solution {Z : Scheme.{0}} {k : Z ⟶ S'} {h : Z ⟶ S} (hh : h = k ≫ σ) (a b c : Over.mk k ⟶ G')
    (A B C : Over.mk h ⟶ G) (ha : A.left = a.left ≫ φ) (hb : B.left = b.left ≫ φ) (hc : C.left = c.left ≫ φ) :
    (lift A (lift B C)).left = adjPair3 gp a b c := by
  subst hh
  obtain rfl : A = pushHom gp (Over.mk k) a := Over.OverMorphism.ext ha
  obtain rfl : B = pushHom gp (Over.mk k) b := Over.OverMorphism.ext hb
  obtain rfl : C = pushHom gp (Over.mk k) c := Over.OverMorphism.ext hc
  rfl
end GlobalTheory
