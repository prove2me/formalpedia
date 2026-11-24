-- Prove2me | solution 1 for GlobalTheory.BK.ringAct_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:31:22.564827+00:00
-- url     : https://prove2.me/submissions/2418a9aa-14bf-4061-a6dc-50ed4d107e9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Theorems.Thm_GlobalTheory_BK_ringAct_X_pow

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
variable {K : Type} [NormedField K] (l : ℕ) {e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero a] [TameDescentExponentData K l e a]
variable {l}
namespace GlobalTheory.BK
theorem _root_.solution (g : TameGal K l e a) : ringAct g (fun _ => E K l e) = fun _ => E K l e := by
  ext1 τ
  have := congrFun (ringAct_X_pow g) τ
  rw [ringAct_apply] at this ⊢
  rw [E, map_add, this, map_natCast]
end GlobalTheory.BK
