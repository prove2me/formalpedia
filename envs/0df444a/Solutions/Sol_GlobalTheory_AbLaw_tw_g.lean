-- Prove2me | solution 1 for GlobalTheory.AbLaw.tw_g
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:22.197705+00:00
-- url     : https://prove2.me/submissions/64846a25-2f19-4c92-893e-0a138cdef990

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.AbLaw
theorem _root_.solution (M H : LB X) (t : ℤ) (p q : M.ι × H.ι) :
    (tw M H t).g p q =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) ≤ M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
      res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) ≤ H.U p.2 ⊓ H.U q.2) (H.g p.2 q.2) ^ t := by
  change _ * (res _ (H.g p.2 q.2 ^ (-t)))⁻¹ = _
  rw [map_zpow, zpow_neg, inv_inv]
  rfl
end GlobalTheory.AbLaw
