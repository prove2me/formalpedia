-- Prove2me | solution 1 for GlobalTheory.TorusQuotientLift.isWt_appLE_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:16:05.867517+00:00
-- url     : https://prove2.me/submissions/c66b7b81-ce29-4865-8aa9-915d35e3d503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
open GlobalTheory GlobalTheory.TorusQuotientLift
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
variable {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'} {V : G.left.Opens} {V' : G'.left.Opens}
namespace GlobalTheory.TorusQuotientLift
theorem _root_.solution {Y : Scheme.{0}} (r : G.left ⟶ Y)
    (hr : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ r = g.left ≫ r)
    (U : Y.Opens) (h : V ≤ r ⁻¹ᵁ U) (c : Γ(Y, U)) : IsWt i V ((r.appLE U V h).hom c) 0 := fun Z t g h₁ h₂ => by
  rw [← chV_val, chV_zero, Units.val_one, _root_.one_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [hr Z t g]
end GlobalTheory.TorusQuotientLift
