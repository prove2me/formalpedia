-- Prove2me | solution 1 for GlobalTheory.BXOf.prod_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:55:35.347241+00:00
-- url     : https://prove2.me/submissions/17750ac1-0da5-4b60-a79d-e17776b4dfa0

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
theorem _root_.solution (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k : Fin 2, h ((lift x y).left ≫ (![(lift (snd G G) (fst G G)).left, 𝟙 (G ⊗ G).left] k)) ^ (![1, -1] k : ℤ) =
      h (lift y x).left * (h (lift x y).left)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (lift x y ≫ lift (snd G G) (fst G G)).left ^ (1 : ℤ) * h ((lift x y).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [comp_lift, lift_fst, lift_snd, Category.comp_id, zpow_one, _root_.zpow_neg_one]
end GlobalTheory.BXOf
