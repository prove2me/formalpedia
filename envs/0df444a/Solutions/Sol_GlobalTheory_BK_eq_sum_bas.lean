-- Prove2me | solution 1 for GlobalTheory.BK.eq_sum_bas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:46:39.794501+00:00
-- url     : https://prove2.me/submissions/b2a66e00-fa22-4767-bb97-1b67b075eb51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
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



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {K : Type} [NormedField K] {a : ℕ} {ι κ : Type}
namespace GlobalTheory.BK
theorem _root_.solution [Fintype ι] [DecidableEq ι] (v : Vec K a ι) :
    v = ∑ i, (fun τ => v τ i) • (bas i : Vec K a ι) := by
  ext1 τ
  ext1 j
  simp [bas, Finset.sum_apply, Pi.single_apply]
end GlobalTheory.BK
