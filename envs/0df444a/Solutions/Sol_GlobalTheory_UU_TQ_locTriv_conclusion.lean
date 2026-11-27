-- Prove2me | solution 1 for GlobalTheory.UU.TQ.locTriv_conclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:22.07132+00:00
-- url     : https://prove2.me/submissions/93339984-c1ba-4a6c-af3e-a759d3199d87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Statements_LocalTrivialization_LocTrivOfRetraction
import Theorems.Thm_GlobalTheory_FunDescent_hom_ext
import Theorems.Thm_GlobalTheory_ToSplit_act_comp
import Theorems.Thm_GlobalTheory_TorsorUnit_act_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU
namespace TQ
theorem _root_.solution {G : Over S} [GrpObj G] (Q : TQ G X) :
    Mono Q.i ∧ Flat Q.q.left ∧ Surjective Q.q.left ∧ (Smooth G.hom → Smooth Q.B.hom) ∧
      ∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ Q.q = g' ≫ Q.q ↔ ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ Q.i) * g := by
  have := Q.q_hom
  refine ⟨⟨fun a b e => Q.isKernel.hom_ext e (toUnit_unique _ _)⟩, Q.q_flat, Q.q_surj, fun _ => Q.isAb.smooth,
    fun Z g g' => ⟨fun e => ?_, ?_⟩⟩
  · have w : (g' * g⁻¹) ≫ Q.q = toUnit Z ≫ η[Q.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
      rfl
    exact ⟨Q.isKernel.lift _ _ w, by rw [Q.isKernel.lift_fst, inv_mul_cancel_right]⟩
  · rintro ⟨t, rfl⟩
    exact (Q.act_comp t g).symm
end TQ
end GlobalTheory.UU
