-- Prove2me | solution 1 for GlobalTheory.CubeLift.pt_torusMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:33.782828+00:00
-- url     : https://prove2.me/submissions/ff160781-fe9e-4da4-ae2c-01d5d934ef4e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective

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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)
variable {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z Z' V : Over S}
namespace GlobalTheory.CubeLift
theorem _root_.solution (a b c : X →+ Y) : pt (SplitTorus.torusMap S a) (SplitTorus.torusMap S b) (SplitTorus.torusMap S c) = SplitTorus.torusMap S (tri a b c) := by
  refine SplitTorus.hom_ext fun p => ?_
  obtain ⟨x, y, z⟩ := p
  rw [pt, SplitTorus.val_ofVal, SplitTorus.val_torusMap]
  simp only [AddMonoidHom.coprod_apply, toMul_add, Units.val_mul, SplitTorus.valHom_apply,
    SplitTorus.val_torusMap, tri]
  rw [← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id,
    SplitTorus.val_add, SplitTorus.val_add]
end GlobalTheory.CubeLift
