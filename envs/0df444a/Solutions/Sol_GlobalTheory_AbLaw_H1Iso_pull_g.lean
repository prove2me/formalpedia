-- Prove2me | solution 1 for GlobalTheory.AbLaw.H1Iso.pull_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:52:57.119967+00:00
-- url     : https://prove2.me/submissions/954f37ee-7d71-46be-86d7-7cb39c07ef48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen

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
open GlobalTheory.AbLaw.H1Iso
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLaw.H1Iso
theorem _root_.solution (M : LB X) (e : Y ⟶ X) (j j' : (M.pull e).ι) :
    ((M.pull e).g j j').val =
      pb e (le_pre_inf e (inf_le_left.trans (pull_U_le M e j)) (inf_le_right.trans (pull_U_le M e j')) :
        (M.pull e).U j ⊓ (M.pull e).U j' ≤ e ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)))
        (M.g (j PUnit.unit) (j' PUnit.unit)).val := by
  change ((∏ k : PUnit, _ : Γ(Y, _)ˣ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  rfl
end GlobalTheory.AbLaw.H1Iso
