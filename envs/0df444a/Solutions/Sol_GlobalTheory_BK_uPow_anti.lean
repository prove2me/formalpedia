-- Prove2me | solution 1 for GlobalTheory.BK.uPow_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:45:22.978002+00:00
-- url     : https://prove2.me/submissions/98940129-7183-4166-8698-5a5053ea1621

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta

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
variable {K : Type} [NormedField K] {a : ℕ} {ι κ : Type}
namespace GlobalTheory.BK
theorem _root_.solution {m n : ℕ} (h : m ≤ n) : uPow K a ι n ≤ uPow K a ι m :=
  fun _ hv τ i => (pow_dvd_pow _ h).trans (hv τ i)
end GlobalTheory.BK
