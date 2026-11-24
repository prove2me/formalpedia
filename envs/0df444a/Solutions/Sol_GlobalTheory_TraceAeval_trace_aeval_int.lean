-- Prove2me | solution 1 for GlobalTheory.TraceAeval.trace_aeval_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:12:00.61717+00:00
-- url     : https://prove2.me/submissions/ed9f186f-2544-4906-ac07-367331e0dcab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq
import Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_matrix
import Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceAeval
open Module
namespace GlobalTheory.TraceAeval
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (p : ℤ[X]) :
    (((aeval A p).trace : ℤ) : ℂ)
      = ((A.map (Int.castRingHom ℂ)).charpoly.roots.map fun z => aeval z p).sum := by
  rw [← trace_aeval_map, ← aeval_map_algebraMap ℂ, trace_aeval_matrix]
  simp only [eval_map_algebraMap]
end GlobalTheory.TraceAeval
