-- Prove2me | solution 1 for GlobalTheory.adjPair2_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:11:39.676539+00:00
-- url     : https://prove2.me/submissions/17e115da-889a-4963-9a5f-8de4b42ce498

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
theorem _root_.solution {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (sq : IsSquare φ φ₂) {T : Over S'} (a b : T ⟶ G') :
    (lift a b).left ≫ φ₂ = adjPair2 gp a b := by
  refine pullback.hom_ext (f := G.hom) (g := G.hom) ?_ ?_
  · have e₁ : (lift a b).left ≫ (fst G' G').left = a.left := congrArg (fun q => q.left) (lift_fst a b)
    have e₂ : adjPair2 gp a b ≫ (fst G G).left = a.left ≫ φ :=
      congrArg (fun q => q.left) (lift_fst (pushHom gp T a) (pushHom gp T b))
    show ((lift a b).left ≫ φ₂) ≫ (fst G G).left = adjPair2 gp a b ≫ (fst G G).left
    rw [e₂, Category.assoc, sq.1, ← Category.assoc, e₁]
  · have e₁ : (lift a b).left ≫ (snd G' G').left = b.left := congrArg (fun q => q.left) (lift_snd a b)
    have e₂ : adjPair2 gp a b ≫ (snd G G).left = b.left ≫ φ :=
      congrArg (fun q => q.left) (lift_snd (pushHom gp T a) (pushHom gp T b))
    show ((lift a b).left ≫ φ₂) ≫ (snd G G).left = adjPair2 gp a b ≫ (snd G G).left
    rw [e₂, Category.assoc, sq.2, ← Category.assoc, e₁]
end GlobalTheory
