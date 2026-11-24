-- Prove2me | solution 1 for GlobalTheory.Mem.ZetaPole.logFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:15.886814+00:00
-- url     : https://prove2.me/submissions/78b3bbf4-26ad-4601-b508-aa5f9fddd854

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
import Theorems.Thm_GlobalTheory_Mem_ZetaPole_rpow_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.ZetaPole
namespace GlobalTheory.Mem.ZetaPole
theorem _root_.solution {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : 0 ≤ logFactor n s := by
  have h1 := rpow_lt_one hn hs
  have h2 : 0 ≤ (n : ℝ) ^ (-s) := by positivity
  unfold logFactor
  have := Real.log_nonpos (x := 1 - (n : ℝ) ^ (-s)) (by linarith) (by linarith)
  linarith
end GlobalTheory.Mem.ZetaPole
