-- Prove2me | solution 1 for GlobalTheory.UU.IsWt.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:45.73071+00:00
-- url     : https://prove2.me/submissions/5e4d237e-caaf-4b34-9727-504e3f22e171

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
variable {S S' : Scheme.{0}}
attribute [instance] TQ.grp TQ.comm
variable {X : Type} [AddCommGroup X]
variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V V' : G.left.Opens}
namespace GlobalTheory.UU
namespace IsWt
theorem _root_.solution {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ) : IsWt i V (u⁻¹).val (-χ) := by
  intro Z t g h₁ h₂
  have e1 : (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (u⁻¹).val * (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u.val = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e2 : (g.left.appLE V ⊤ h₂).hom (u⁻¹).val * (g.left.appLE V ⊤ h₂).hom u.val = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e3 : t.left.appTop.hom (charUnit S X (-χ)).val * t.left.appTop.hom (charUnit S X χ).val = 1 := by
    rw [← chV_val, ← chV_val, ← Units.val_mul, ← chV_add, neg_add_cancel, chV_zero, Units.val_one]
  have e4 := hu Z t g h₁ h₂
  linear_combination (-((((t ≫ i) * g).left.appLE V ⊤ h₁).hom (u⁻¹).val * (g.left.appLE V ⊤ h₂).hom (u⁻¹).val *
      (g.left.appLE V ⊤ h₂).hom u.val)) * e3 - (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (u⁻¹).val * e2 -
    t.left.appTop.hom (charUnit S X (-χ)).val * (g.left.appLE V ⊤ h₂).hom (u⁻¹).val *
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom (u⁻¹).val * e4 +
    t.left.appTop.hom (charUnit S X (-χ)).val * (g.left.appLE V ⊤ h₂).hom (u⁻¹).val * e1
end IsWt
end GlobalTheory.UU
