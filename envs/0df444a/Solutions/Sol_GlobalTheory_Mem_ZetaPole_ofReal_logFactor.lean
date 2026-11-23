-- Prove2me | solution 1 for GlobalTheory.Mem.ZetaPole.ofReal_logFactor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:07.212793+00:00
-- url     : https://prove2.me/submissions/c6e77c5e-453f-47a4-8777-623d3168cbe1

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
theorem _root_.solution {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) :
    ((logFactor n s : ℝ) : ℂ) = -Complex.log (1 - (n : ℂ) ^ (-(s : ℂ))) := by
  have h1 := rpow_lt_one hn hs
  unfold logFactor
  rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp
end GlobalTheory.Mem.ZetaPole
