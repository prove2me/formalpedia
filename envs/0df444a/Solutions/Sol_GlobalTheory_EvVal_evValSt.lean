-- Prove2me | solution 1 for GlobalTheory.EvVal.evValSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:40.746956+00:00
-- url     : https://prove2.me/submissions/803860c0-5ba6-439f-943e-5855fa36ea21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Theorems.Thm_GlobalTheory_EvVal_existsUnique_sec_eq_mul_gen
import Theorems.Thm_GlobalTheory_EvVal_powFrame_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_linComb_cover


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
open GlobalTheory GlobalTheory.EvVal
namespace GlobalTheory.EvVal
theorem _root_.solution : ∀ S : Scheme.{0}, EvValSt (S := S) := by
  intro S P N T z e he s
  exact existsUnique_sec_eq_mul_gen _ (TLinPf.linComb_cover P.L P.isLB _ _)
    (pullSec P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => (N : ℤ)) (ptSecT P.A z).left
      (fun _ => z.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd])
      (val_le P.A P.L z) s)
    (powFrame P.A P.L z e N) (powFrame_isGen P.A P.L z e he N)
end GlobalTheory.EvVal
