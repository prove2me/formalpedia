-- Prove2me | solution 1 for GlobalTheory.grpPullback_prod_secondLaw_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:05.199304+00:00
-- url     : https://prove2.me/submissions/2ea08736-b406-4b47-aaff-069d767ae3e2

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
import Theorems.Thm_GlobalTheory_adjProd_ulift

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
omit [IsCommMonObj G']
namespace GlobalTheory
theorem _root_.solution {T : Over S'} (a b c : T ⟶ G') {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ i, h (adjPair3 gp a b c ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) i) ^ lawε i =
      h (adjPair2 gp a (b * c)) * (h (adjPair2 gp a b))⁻¹ * (h (adjPair2 gp a c))⁻¹ := by
  rw [adjProd_ulift, adjPair2, adjPair2, adjPair2, map_mul, adjPair3]
  generalize pushHom gp T a = A
  generalize pushHom gp T b = B
  generalize pushHom gp T c = C
  have e₀ : lift A (lift B C) ≫ lift (x3 G 0) (padd G (x3 G 1) (x3 G 2)) = lift A (B * C) := by
    rw [comp_lift]
    congr 1
    · simp [x3]
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
  have e₁ : lift A (lift B C) ≫ lift (x3 G 0) (x3 G 1) = lift A B := by simp [x3, comp_lift]
  have e₂ : lift A (lift B C) ≫ lift (x3 G 0) (x3 G 2) = lift A C := by simp [x3, comp_lift]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (fun q => h q.left) e₀) (congrArg (fun q => (h q.left)⁻¹) e₁))
    (congrArg (fun q => (h q.left)⁻¹) e₂)
end GlobalTheory
