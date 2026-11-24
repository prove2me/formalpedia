-- Prove2me | solution 1 for GlobalTheory.TraceAeval.trace_aeval_powMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:22:16.571889+00:00
-- url     : https://prove2.me/submissions/e6cc2927-2a49-47ae-abe1-96092555dd89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq
import Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_int
import Theorems.Thm_GlobalTheory_TraceAeval_powMat_map
import Theorems.Thm_GlobalTheory_TraceAeval_charpoly_powMat

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
theorem _root_.solution {ψ : ℤ[X]} (h : ψ.Monic) (p : ℤ[X]) :
    (((aeval (powMat ψ.natDegree ψ) p).trace : ℤ) : ℂ)
      = ((ψ.aroots ℂ).map fun z => aeval z p).sum := by
  rw [trace_aeval_int, powMat_map _ _ h, ← h.natDegree_map (Int.castRingHom ℂ),
    charpoly_powMat (h.map _)]
  rfl
end GlobalTheory.TraceAeval
