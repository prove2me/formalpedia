-- Prove2me | solution 1 for GlobalTheory.TraceAeval.trace_aeval_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:03:00.735122+00:00
-- url     : https://prove2.me/submissions/704e7ced-72dd-47fe-83b0-9cc29d7e38d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq
import Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_end

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ[X]) :
    (aeval A p).trace = (A.charpoly.roots.map fun z => p.eval z).sum := by
  rw [← Matrix.charpoly_toLin', ← trace_aeval_end, ← Matrix.trace_toLin'_eq]
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)) A p).symm
end GlobalTheory.TraceAeval
