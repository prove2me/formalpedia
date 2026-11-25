-- Prove2me | solution 1 for GlobalTheory.UU.IsWt.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:49.926981+00:00
-- url     : https://prove2.me/submissions/9a8f6980-b420-4d0a-87a1-ac97b34a3b1b

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
theorem _root_.solution {u v : Γ(G.left, V)} {χ χ' : X} (hu : IsWt i V u χ) (hv : IsWt i V v χ') :
    IsWt i V (u * v) (χ + χ') := by
  intro Z t g h₁ h₂
  simp only [map_mul]
  rw [hu Z t g h₁ h₂, hv Z t g h₁ h₂, ← chV_val, ← chV_val, ← chV_val, chV_add, Units.val_mul]
  ring
end IsWt
end GlobalTheory.UU
