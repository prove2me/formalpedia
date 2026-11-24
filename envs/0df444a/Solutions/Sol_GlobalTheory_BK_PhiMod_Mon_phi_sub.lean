-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.Mon_phi_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:48.761776+00:00
-- url     : https://prove2.me/submissions/d655b575-0be6-402e-8454-83416b1785fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_PhiMod_EN_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_Mon_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_zeta_phi_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (m : Vec K a ι) : P.Mon (P.phi m - m) = -P.cls (P.EN m) := by
  rw [Mon_apply, zeta_phi_sub, map_sub P.EN, ← EN_apply, sub_sub_cancel_left, map_neg]
end GlobalTheory.BK.PhiMod
