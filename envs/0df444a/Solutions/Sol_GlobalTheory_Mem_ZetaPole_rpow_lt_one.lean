-- Prove2me | solution 1 for GlobalTheory.Mem.ZetaPole.rpow_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:09.677183+00:00
-- url     : https://prove2.me/submissions/ac925eb3-bf86-47e6-90e7-856621de1d79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite

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
theorem _root_.solution {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : (n : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by linarith)
end GlobalTheory.Mem.ZetaPole
