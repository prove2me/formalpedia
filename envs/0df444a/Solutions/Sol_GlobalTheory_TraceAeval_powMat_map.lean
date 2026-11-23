-- Prove2me | solution 1 for GlobalTheory.TraceAeval.powMat_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:38.757787+00:00
-- url     : https://prove2.me/submissions/9d604bb9-e500-488e-90bc-0fb2a7a86665

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
open Polynomial
open Module
namespace GlobalTheory.TraceAeval
namespace _root_.GlobalTheory.TraceAeval
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) {ψ : R[X]} (h : ψ.Monic) :
    (_root_.GlobalTheory.TraceAeval.powMat n ψ).map f = _root_.GlobalTheory.TraceAeval.powMat n (ψ.map f) := by
  ext i j
  simp only [_root_.GlobalTheory.TraceAeval.powMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic f h, Polynomial.map_pow,
    Polynomial.map_X]
end _root_.GlobalTheory.TraceAeval
end GlobalTheory.TraceAeval
