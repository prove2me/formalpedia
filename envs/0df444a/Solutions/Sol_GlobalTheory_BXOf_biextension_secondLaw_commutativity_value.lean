-- Prove2me | solution 1 for GlobalTheory.BXOf.biextension_secondLaw_commutativity_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:48.005181+00:00
-- url     : https://prove2.me/submissions/49607ec6-2299-435c-b034-b1e7a4f1d64f

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
import Theorems.Thm_GlobalTheory_BXOf_val_pull3
import Theorems.Thm_GlobalTheory_BXOf_onObjOf3_x_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr


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
namespace GlobalTheory.BXOf
theorem _root_.solution (hJ : Good P z J) (x y y' : T ⟶ G) :
    val β.law2 (lift x (lift y y')).left z J = val β.law2 (lift x (lift y' y)).left z J := by
  have e := (val_corr hJ β.comm2 (lift x (lift y y')).left).trans (val_pull3 _ hJ _ _ _ _)
  obtain ⟨a₀, a₁, a₂⟩ := onObjOf3_x_eq x y y'
  rwa [a₀, a₁, a₂] at e
end GlobalTheory.BXOf
