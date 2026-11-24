-- Prove2me | solution 1 for GlobalTheory.BK.eq_zero_of_mem_uPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:24.084866+00:00
-- url     : https://prove2.me/submissions/5373b3c2-52ad-430a-bb8d-ea00fb479737

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
theorem _root_.solution {v : Vec K a ι} (h : ∀ m, v ∈ uPow K a ι (m + 1)) : v = 0 := by
  ext τ i n
  simpa using X_pow_dvd_iff.1 (h n τ i) n (Nat.lt_succ_self n)
end GlobalTheory.BK
