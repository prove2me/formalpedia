-- Prove2me | solution 1 for GlobalTheory.AbLaw.H1Iso.rs_g_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:52:57.68432+00:00
-- url     : https://prove2.me/submissions/4ab5a1cd-591b-4cee-9b27-b599d91b983b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen
import Theorems.Thm_GlobalTheory_AbLaw_H1Iso_val_res

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
theorem _root_.solution {M : LB X} (hM : M.IsLB) (k : M.ι) {W : X.Opens} (h : W ≤ M.U k ⊓ M.U k) :
    rs X h (M.g k k).val = 1 := by
  have h' := congrArg (fun u => rs X (h.trans inf_le_left : W ≤ M.U k) (Units.val u)) (hM.g_self k)
  simp only [val_res, rs_rs, Units.val_one, map_one] at h'
  exact h'
end GlobalTheory.AbLaw.H1Iso
