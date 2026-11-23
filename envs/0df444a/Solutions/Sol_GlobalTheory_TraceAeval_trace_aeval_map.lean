-- Prove2me | solution 1 for GlobalTheory.TraceAeval.trace_aeval_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:38.960341+00:00
-- url     : https://prove2.me/submissions/74613724-219e-4c42-93b7-009f1345735f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq

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
theorem _root_.solution {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) ℤ)
    (p : ℤ[X]) :
    (aeval (A.map (Int.castRingHom R)) p).trace = (((aeval A p).trace : ℤ) : R) := by
  have := aeval_algHom_apply ((Int.castRingHom R).mapMatrix (m := Fin n)).toIntAlgHom A p
  have h2 : aeval (A.map (Int.castRingHom R)) p = (aeval A p).map (Int.castRingHom R) := this
  rw [h2]
  simp [Matrix.trace]
end GlobalTheory.TraceAeval
