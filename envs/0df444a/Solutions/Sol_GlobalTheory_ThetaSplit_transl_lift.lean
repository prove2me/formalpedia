-- Prove2me | solution 1 for GlobalTheory.ThetaSplit.transl_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:33:02.845748+00:00
-- url     : https://prove2.me/submissions/3800fc46-5ae6-4d72-97e2-480b3dfa27ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ThetaSplit
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
namespace GlobalTheory.ThetaSplit
theorem _root_.solution (c : 𝟙_ (Over S) ⟶ A) : transl c ≫ (lift (toUnit A) (𝟙 A)).left =
    (lift (toUnit A) (𝟙 A)).left ≫ (Out.translT A c).left := by
  rw [← Over.comp_left, ← Over.comp_left, CommutatorPairing.lift_translT, comp_lift, comp_toUnit, Category.comp_id]
end GlobalTheory.ThetaSplit
