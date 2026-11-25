-- Prove2me | solution 1 for GlobalTheory.BK.Hom.onPol_Mon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:25:23.038963+00:00
-- url     : https://prove2.me/submissions/65941c3b-5c4b-4851-8f99-de3e9f94bdf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Theorems.Thm_GlobalTheory_BK_PhiMod_Mon_apply
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_Hom_app_EN
import Theorems.Thm_GlobalTheory_BK_Hom_app_zeta
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe


attribute [local simp] GlobalTheory.BK.Hom.onPol_cls

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
open GlobalTheory.BK.Hom
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
namespace GlobalTheory.BK.Hom
theorem _root_.solution (y : Vec K a ι) : F.onPol (P.Mon y) = Q.Mon (F.app y) := by
  rw [PhiMod.Mon_apply, onPol_cls, map_sub, app_EN, map_smul, app_zeta, PhiMod.Mon_apply]
end GlobalTheory.BK.Hom
