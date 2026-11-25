-- Prove2me | solution 1 for GlobalTheory.BXOf.lift_four_points_comp_projections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:04:58.589812+00:00
-- url     : https://prove2.me/submissions/9760523a-dd1e-45fc-a6de-0a20b50c9d47

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawCommutativityValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BXOf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)
  {T : Over S₀} {z : T.left} {J : (T.left ⟶ (G ⊗ G).left) → P.ι}
omit [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.BXOf
theorem _root_.solution (x x' x'' y : T ⟶ G) : lift x (lift x' (lift x'' y)) ≫ x4 G 0 = x ∧
    lift x (lift x' (lift x'' y)) ≫ x4 G 1 = x' ∧ lift x (lift x' (lift x'' y)) ≫ x4 G 2 = x'' ∧
    lift x (lift x' (lift x'' y)) ≫ x4 G 3 = y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [x4]
end GlobalTheory.BXOf
