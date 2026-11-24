-- Prove2me | solution 1 for GlobalTheory.Mem.ZetaPole.logFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:15.280855+00:00
-- url     : https://prove2.me/submissions/e821aadf-1671-4d70-af87-59c238bb52ad

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
theorem _root_.solution {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 1 ≤ s) : logFactor n s ≤ logFactor n 1 := by
  have h1 := rpow_lt_one hn one_pos
  have h2 : (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) (by linarith)
  unfold logFactor
  have := Real.log_le_log (x := 1 - (n : ℝ) ^ (-1 : ℝ)) (y := 1 - (n : ℝ) ^ (-s))
    (by linarith) (by linarith)
  linarith
end GlobalTheory.Mem.ZetaPole
