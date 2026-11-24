-- Prove2me | solution 1 for GlobalTheory.BK.ringAct_NTot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:42.83701+00:00
-- url     : https://prove2.me/submissions/b4706f06-b163-4d1a-afd8-66b311efb367

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_coeff_N
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
variable {K : Type} [NormedField K] (l : ℕ) {e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero a] [TameDescentExponentData K l e a]
variable {l}
namespace GlobalTheory.BK
theorem _root_.solution (g : TameGal K l e a) (f : ZMod a → K⟦X⟧) :
    ringAct g (NTot f) = NTot (ringAct g f) := by
  ext τ n
  simp only [ringAct_apply, NTot, coeff_rescale, coeff_N]
  ring
end GlobalTheory.BK
