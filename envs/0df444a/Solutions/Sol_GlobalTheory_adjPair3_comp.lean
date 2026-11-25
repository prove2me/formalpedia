-- Prove2me | solution 1 for GlobalTheory.adjPair3_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:09:21.921446+00:00
-- url     : https://prove2.me/submissions/2e420439-5d9d-4187-9bd6-82777c31a9ba

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
theorem _root_.solution {T T' : Over S'} (r : T' ⟶ T) (a b c : T ⟶ G') :
    r.left ≫ adjPair3 gp a b c = adjPair3 gp (r ≫ a) (r ≫ b) (r ≫ c) := by
  let U : Over.mk (T'.hom ≫ σ) ⟶ Over.mk (T.hom ≫ σ) := Over.homMk r.left (by
    show r.left ≫ T.hom ≫ σ = T'.hom ≫ σ
    rw [← Category.assoc, Over.w r])
  have e : ∀ a : T ⟶ G', U ≫ pushHom gp T a = pushHom gp T' (r ≫ a) := fun a =>
    Over.OverMorphism.ext (Category.assoc r.left a.left φ).symm
  show (U ≫ lift (pushHom gp T a) (lift (pushHom gp T b) (pushHom gp T c))).left = _
  rw [comp_lift, comp_lift, e, e, e]; rfl
end GlobalTheory
