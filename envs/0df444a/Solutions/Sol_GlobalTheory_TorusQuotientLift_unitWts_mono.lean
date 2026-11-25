-- Prove2me | solution 1 for GlobalTheory.TorusQuotientLift.unitWts_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:46:48.049338+00:00
-- url     : https://prove2.me/submissions/63430430-5c2e-4bd1-9759-73a5d676c723

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
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_res


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
theorem _root_.solution {W : G.left.Opens} (h : W ≤ V) : unitWts i V ≤ unitWts i W :=
  fun _ ⟨u, hu⟩ => ⟨Units.map (rs h).toMonoidHom u, hu.res h⟩
end GlobalTheory.TorusQuotientLift
